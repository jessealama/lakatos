import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import {
  interruptedBy,
  type InterruptSignal,
} from "../../../../src/interrupt.js";
import { isProveStatus, type ProveStatus } from "../../../../src/szs.js";

/** One #thales_prove verdict line: the contract printed by ThalesDsl.
 * Counterexample values outside the JS safe-integer range travel as
 * decimal strings. */
export interface LeanVerdict {
  identity: [string, string, string];
  szs: ProveStatus;
  reason: string;
  counterexample?: Record<string, number | string>;
  /** Theorem only: the non-standard axioms the proof depends on. */
  axioms?: string[];
}

/** One artifact whose Lean run failed or broke the verdict contract;
 * only its own annotations are affected. */
export interface FileFailure {
  file: string;
  messages: string[];
}

export type LeanRunResult =
  | {
      kind: "completed";
      verdicts: LeanVerdict[];
      failures: FileFailure[];
      diagnostics: string[];
    }
  | { kind: "no-project"; message: string }
  | { kind: "failed"; stdout: string; stderr: string }
  | { kind: "interrupted"; signal: InterruptSignal };

// Exported so test timeouts can be sized from the containment budget.
export const LEAN_TIMEOUT_MS = 300_000;
export const BUILD_TIMEOUT_MS = 600_000;
export const EMIT_TIMEOUT_MS = 120_000;

/** Frames each verdict line: stdout is also Lean's diagnostic stream, so
 * only framed lines are part of the contract. ThalesDsl's
 * `Verdict.sentinel` prints it. */
export const VERDICT_SENTINEL = "thales-verdict:";

/** Locate the ThalesDsl lake project: walk up from this module looking for
 * a lakefile here or under engines/thales — covers the source tree, the
 * compiled dist/ tree, and (by failing) installs without the Lean engine. */
export function findEngineRoot(
  from: string = fileURLToPath(import.meta.url),
): string | undefined {
  let dir = path.dirname(from);
  for (;;) {
    for (const c of [dir, path.join(dir, "engines", "thales")]) {
      if (existsSync(path.join(c, "lakefile.lean"))) return c;
    }
    const parent = path.dirname(dir);
    if (parent === dir) return undefined;
    dir = parent;
  }
}

/** What runLean needs back from a spawn; a subset of spawnSync's return. */
export interface SpawnOutcome {
  status: number | null;
  signal?: NodeJS.Signals | null;
  stdout: string | null;
  stderr: string | null;
  error?: Error;
}

type Spawn = (
  cmd: string,
  args: string[],
  opts: { cwd: string; encoding: "utf8"; timeout: number },
) => SpawnOutcome;

function isCounterexample(c: unknown): c is Record<string, number | string> {
  return (
    typeof c === "object" &&
    c !== null &&
    !Array.isArray(c) &&
    Object.values(c).every(
      (x) => typeof x === "number" || typeof x === "string",
    )
  );
}

/** A verdict must explain itself: every status but Theorem and
 * CounterSatisfiable carries its reason into the envelope, and the two that
 * drop it are no cheaper for the engine to fill in. */
function isVerdict(v: unknown): v is LeanVerdict {
  if (typeof v !== "object" || v === null) return false;
  const o = v as Record<string, unknown>;
  return (
    Array.isArray(o.identity) &&
    o.identity.length === 3 &&
    o.identity.every((s) => typeof s === "string") &&
    typeof o.szs === "string" &&
    isProveStatus(o.szs) &&
    typeof o.reason === "string" &&
    o.reason.length > 0 &&
    (o.counterexample === undefined || isCounterexample(o.counterexample)) &&
    (o.axioms === undefined ||
      (Array.isArray(o.axioms) &&
        o.axioms.every((a) => typeof a === "string" && a.length > 0)))
  );
}

/** Split one artifact's stdout into verdicts, unframed diagnostic lines,
 * and contract violations. Shared with the engine's check scripts so the
 * channel is parsed and validated in exactly one place. */
export function parseVerdicts(stdout: string): {
  verdicts: LeanVerdict[];
  diagnostics: string[];
  messages: string[];
} {
  const verdicts: LeanVerdict[] = [];
  const diagnostics: string[] = [];
  const messages: string[] = [];
  for (const line of stdout.split("\n")) {
    if (line.trim() === "") continue;
    if (!line.startsWith(VERDICT_SENTINEL)) {
      diagnostics.push(line);
      continue;
    }
    let v: unknown;
    try {
      v = JSON.parse(line.slice(VERDICT_SENTINEL.length));
    } catch {
      messages.push(`unparseable verdict line: ${line}`);
      continue;
    }
    if (!isVerdict(v)) {
      messages.push(`malformed verdict line: ${line}`);
      continue;
    }
    verdicts.push(v);
  }
  return { verdicts, diagnostics, messages };
}

function isEnoent(e: Error | undefined): boolean {
  return e !== undefined && (e as NodeJS.ErrnoException).code === "ENOENT";
}

function failed(r: SpawnOutcome): LeanRunResult {
  return {
    kind: "failed",
    stdout: r.stdout ?? "",
    stderr: (r.stderr ?? "") + (r.error ? `${String(r.error)}\n` : ""),
  };
}

/** Heartbeat-budget override for the artifact runs; e2e suites shrink it
 * to exercise Timeout deterministically. A zero budget is ignored like any
 * other unusable value: Lean reads maxHeartbeats 0 as unlimited, so
 * forwarding it would widen the budget instead of shrinking it. */
function heartbeatArgs(): string[] {
  const v = process.env.LAKATOS_PROVE_HEARTBEATS;
  return v !== undefined && /^\d+$/.test(v) && Number(v) > 0
    ? [`-Dweak.thales.heartbeats=${v}`]
    : [];
}

/** Run one artifact through `lake env lean` under the containment budget.
 * Shared with the engine's check scripts so the argv, the heartbeat
 * override, and the timeout are settled in one place. */
export function runArtifact(
  engineRoot: string,
  file: string,
  spawn: Spawn = spawnSync,
): SpawnOutcome {
  return spawn(
    "lake",
    ["env", "lean", ...heartbeatArgs(), path.resolve(file)],
    { cwd: engineRoot, encoding: "utf8", timeout: LEAN_TIMEOUT_MS },
  );
}

/**
 * Run `lake env lean` over each artifact and collect the sentinel-framed
 * verdict lines. `engineRoot` is the caller's `findEngineRoot()` result —
 * absent means this installation has no Lean engine. `lake build` runs
 * first: the DSL library must be compiled for the pinned toolchain, and a
 * cached build is a fast no-op. Only a build failure or a missing engine
 * aborts the run; a hung, crashed, or contract-breaking artifact is
 * contained in `failures`, and unframed stdout is `diagnostics`. A build
 * or artifact killed by a termination signal stops the run there: the
 * artifacts after it are never started.
 */
const NO_PROJECT: LeanRunResult = {
  kind: "no-project",
  message:
    "the Lean proof engine is not part of this installation; run prove from a lakatos checkout",
};

/** One `lake build` under the shared no-project / interrupt / failure
 * discipline; undefined means the build is healthy. Extra args name
 * further targets beyond the default ones. */
function buildStep(
  engineRoot: string,
  spawn: Spawn,
  targets: string[] = [],
): LeanRunResult | undefined {
  const build = spawn("lake", ["build", ...targets], {
    cwd: engineRoot,
    encoding: "utf8",
    timeout: BUILD_TIMEOUT_MS,
  });
  if (isEnoent(build.error)) {
    return {
      kind: "no-project",
      message:
        "lake was not found on PATH; install the Lean toolchain via elan (https://leanprover-community.github.io/get_started/) and re-run",
    };
  }
  const buildSignal = interruptedBy(build);
  if (buildSignal !== undefined)
    return { kind: "interrupted", signal: buildSignal };
  if (build.error !== undefined || build.status !== 0) return failed(build);
  return undefined;
}

/** The per-artifact lean pass the emission run performs. */
function leanPass(
  leanFiles: string[],
  engineRoot: string,
  spawn: Spawn,
): LeanRunResult {
  const verdicts: LeanVerdict[] = [];
  const failures: FileFailure[] = [];
  const diagnostics: string[] = [];
  for (const file of leanFiles) {
    const run = runArtifact(engineRoot, file, spawn);
    // The signal that killed this artifact killed the run: stop here
    // rather than starting artifacts nobody is waiting for any more.
    const signal = interruptedBy(run);
    if (signal !== undefined) return { kind: "interrupted", signal };
    if (run.error !== undefined || run.status !== 0) {
      // A hung or crashed artifact degrades only its own annotations.
      failures.push({
        file,
        messages: [
          `the Lean run on ${file} failed before reporting its verdicts`,
          ...[run.stdout, run.stderr, run.error && String(run.error)].filter(
            (s): s is string => typeof s === "string" && s.trim() !== "",
          ),
        ],
      });
      continue;
    }
    const parsed = parseVerdicts(run.stdout ?? "");
    diagnostics.push(...parsed.diagnostics);
    if (parsed.messages.length > 0) {
      failures.push({ file, messages: parsed.messages });
      continue;
    }
    verdicts.push(...parsed.verdicts);
  }
  return { kind: "completed", verdicts, failures, diagnostics };
}

/** One emission JSON and where thales-emit renders its artifact. */
export interface EmissionJob {
  jsonFile: string;
  leanFile: string;
}

/**
 * The plain-Lean emission run: build the library and the emitter, render
 * each job's artifact with thales-emit, then run the artifacts the way
 * the lean pass does. A failed emit degrades only its own file — a malformed
 * emission fails that file's annotations, never the run — keyed by the
 * artifact path so the caller attributes it like a failed lean run.
 */
export function runEmission(
  jobs: EmissionJob[],
  engineRoot: string | undefined,
  spawn: Spawn = spawnSync,
): LeanRunResult {
  if (engineRoot === undefined) return NO_PROJECT;
  const unhealthy =
    buildStep(engineRoot, spawn) ??
    buildStep(engineRoot, spawn, ["thales-emit"]);
  if (unhealthy !== undefined) return unhealthy;
  const emitBin = path.join(engineRoot, ".lake", "build", "bin", "thales-emit");
  const failures: FileFailure[] = [];
  const emitted: string[] = [];
  for (const job of jobs) {
    // lake env supplies LEAN_PATH: the emitter imports compiled modules.
    // The job's paths are relative to the caller's cwd, not the engine
    // root the emitter runs in — resolve them the way runArtifact does.
    const run = spawn(
      "lake",
      ["env", emitBin, path.resolve(job.jsonFile), path.resolve(job.leanFile)],
      { cwd: engineRoot, encoding: "utf8", timeout: EMIT_TIMEOUT_MS },
    );
    const signal = interruptedBy(run);
    if (signal !== undefined) return { kind: "interrupted", signal };
    if (run.error !== undefined || run.status !== 0) {
      failures.push({
        file: job.leanFile,
        messages: [
          `thales-emit failed on ${job.jsonFile} before rendering the artifact`,
          ...[run.stdout, run.stderr, run.error && String(run.error)].filter(
            (s): s is string => typeof s === "string" && s.trim() !== "",
          ),
        ],
      });
      continue;
    }
    emitted.push(job.leanFile);
  }
  const pass = leanPass(emitted, engineRoot, spawn);
  if (pass.kind !== "completed") return pass;
  return { ...pass, failures: [...failures, ...pass.failures] };
}
