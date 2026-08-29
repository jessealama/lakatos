#!/usr/bin/env node
import { parseArgs } from "node:util";
import { existsSync, readFileSync, realpathSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { writeEmissionArtifacts } from "../engines/thales/frontend/src/emission-artifacts.js";
import {
  findEngineRoot,
  type LeanRunResult,
  runEmission,
} from "../engines/thales/frontend/src/run.js";
import { generate } from "../engines/pabst/src/codegen.js";
import { runTests } from "../engines/pabst/src/run.js";
import { parseSeed, randomSeed } from "../engines/pabst/src/seed.js";
import {
  EmptyAfterClampError,
  extract,
  type InvalidAnnotation,
  LemmaError,
  parseBody,
  parsePrefix,
  qualifiedName,
  resolveFiles,
  type TypecheckDiagnostic,
  typecheckProject,
} from "../lemma/src/index.js";
import {
  interruptedResults,
  joinProveVerdicts,
  joinRefuteVerdicts,
  type AnnotationResult,
  type Envelope,
  type PropertyIdentity,
} from "./envelope.js";
import { withInterruptGuard, type InterruptSignal } from "./interrupt.js";
import { claimRunDir, RUN_ROOT } from "./run-dir.js";

/** Envelope entries for extraction-level input errors, with their
 * diagnostics echoed to stderr. Any such entry makes the run exit 2.
 * The `file:line:` prefix matches the compile-error diagnostic style. */
function inputErrorResults(
  perFile: { file: string; invalid: InvalidAnnotation[] }[],
): AnnotationResult[] {
  const results = perFile.flatMap(({ file, invalid }) =>
    invalid.map((i) => ({
      file,
      function: qualifiedName(i.functionName, i.className, i.isStatic),
      property: i.propertyName,
      szs: "InputError" as const,
      error: `${file}:${i.line}: ${i.message}`,
    })),
  );
  for (const r of results) console.error(`error: ${r.error}`);
  return results;
}

function formatTsDiagnostic(d: TypecheckDiagnostic): string {
  const site = d.file !== undefined ? `${d.file}:${d.line}: ` : "";
  return `${site}TS${d.code}: ${d.message}`;
}

/** Envelope entries for a program the type-check gate refused: every
 * extractable annotation is InputError — the program it describes never
 * compiled — beside the extraction-level input errors found on the way. */
function typecheckRefusedResults(
  files: string[],
  diagnostics: TypecheckDiagnostic[],
): AnnotationResult[] {
  const rest = diagnostics.length - 1;
  const error =
    `the program does not type check: ${formatTsDiagnostic(diagnostics[0]!)}` +
    (rest > 0 ? ` (and ${rest} more)` : "");
  const results: AnnotationResult[] = [];
  const invalid: { file: string; invalid: InvalidAnnotation[] }[] = [];
  for (const file of files) {
    const extracted = extract(file);
    invalid.push({ file, invalid: extracted.invalid });
    for (const a of extracted.annotations) {
      results.push({
        file,
        function: qualifiedName(a.functionName, a.className, a.isStatic),
        property: a.propertyName,
        szs: "InputError",
        error,
      });
    }
  }
  return [...results, ...inputErrorResults(invalid)];
}

// The module runs from src/ under vitest and dist/src/ as a bin, so
// package.json sits a different number of levels up in each: walk.
function readVersion(): string {
  let dir = path.dirname(fileURLToPath(import.meta.url));
  while (!existsSync(path.join(dir, "package.json"))) {
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("package.json not found");
    dir = parent;
  }
  return JSON.parse(readFileSync(path.join(dir, "package.json"), "utf8"))
    .version as string;
}

/** Envelope fields outside the per-annotation list. */
type EnvelopeMeta = Omit<Envelope, "annotations">;

/** Run metadata every command captures before doing anything. */
function captureMeta(): { version: string; startedAt: string; cwd: string } {
  return {
    version: readVersion(),
    startedAt: new Date().toISOString(),
    cwd: process.cwd(),
  };
}

function emitEnvelope(envelope: Envelope): void {
  console.log(JSON.stringify(envelope, null, 2));
}

/** The output contract for a run that stopped before evaluating
 * anything it planned to: `stopped` accounts for those annotations —
 * NotTried when the engine never reported, User when the run was
 * interrupted — beside the entries that were already resolved, and the
 * documented exit 2. The run stats stay out: a run that did not finish
 * knows no counts. */
function stoppedExit(
  meta: EnvelopeMeta,
  plan: Plan,
  stopped: AnnotationResult[],
): number {
  emitEnvelope({
    ...meta,
    annotations: [...stopped, ...plan.untried, ...plan.inputErrors],
  });
  return 2;
}

/** Both engines refuse a domain they cannot represent as written; the stub
 * commands untry everything, with no kind, and say so their own way. */
function noteUnsupportedRanges(untried: AnnotationResult[]): void {
  const n = untried.filter((u) => u.kind === "unsupported-range").length;
  if (n > 0)
    console.error(
      `lakatos: ${n} annotation${n === 1 ? "" : "s"} not tried (unsupported range)`,
    );
}

/** What one command's codegen produced, normalized across engines. */
interface Plan {
  /** Annotations the engine will attempt; the verdict join accounts for each. */
  identities: PropertyIdentity[];
  /** Annotations already resolved at codegen time, in envelope form. */
  untried: AnnotationResult[];
  /** Extraction-level input errors, already echoed to stderr. */
  inputErrors: AnnotationResult[];
  /** Artifacts this invocation generated — the only ones the run may touch. */
  outFiles: string[];
  /** Envelope fields only this command carries (refute's seed and count). */
  meta: Partial<EnvelopeMeta>;
  /** Envelope fields that hold only when there was nothing to run: refute
   * reports zero tests passed and failed, which an interrupted run cannot. */
  emptyMeta: Partial<EnvelopeMeta>;
  /** Exit code when there is nothing to run and no input errors. Zero for a
   * real engine — nothing to disprove is a clean run — but the stub commands
   * report 1: they never attempted the work they were asked for. */
  emptyExit: number;
}

/** One engine's run, normalized. Diagnostics reach stderr inside the
 * adapter; the runner owns the envelope and the exit code. */
type Outcome =
  | {
      /** The engine never reported: annotations were produced but not evaluated. */
      kind: "unhealthy";
      messages: string[];
    }
  | {
      /** A termination signal stopped the engine mid-run. */
      kind: "interrupted";
      signal: InterruptSignal;
    }
  | {
      kind: "completed";
      annotations: AnnotationResult[];
      meta: Partial<EnvelopeMeta>;
      /** The engine failed on part of the run: exit 2 beside the verdicts. */
      degraded: boolean;
      /** The engine refuted something: the documented exit 1. */
      refuted: boolean;
    };

interface Spine {
  /** `runDir` is this invocation's artifact root; the engine joins its own
   * name onto it and never learns where the root came from. */
  plan(files: string[], runDir: string): Plan;
  /** Absent for a command with no engine — its plan yields no artifacts.
   * `runDir` is the same root the plan was given. */
  run?(plan: Plan, runDir: string): Outcome;
}

/** The pipeline every command shares: resolve files, capture run meta, run
 * the engine's codegen, and turn its outcome into one envelope and one exit
 * code. Only the codegen, the run, the verdict join, and the two exit-code
 * contributions are engine-specific. */
function runCommand(spine: Spine, patterns: string[]): number {
  const files = resolve(patterns);
  const base = captureMeta();
  // The gate sits before claimRunDir so a refused run leaves no empty run
  // directory, and before any codegen so no engine sees uncompilable input.
  const check = typecheckProject(
    process.cwd(),
    path.resolve(RUN_ROOT, "typecheck.tsbuildinfo"),
  );
  if (check.kind === "skipped") {
    console.error(
      check.reason === "no-tsconfig"
        ? "lakatos: no tsconfig.json; skipping type check"
        : "lakatos: tsconfig.json names no files; skipping type check",
    );
  } else if (check.kind === "failed") {
    for (const d of check.diagnostics)
      console.error(`error: ${formatTsDiagnostic(d)}`);
    const annotations = typecheckRefusedResults(files, check.diagnostics);
    const n = annotations.length;
    console.error(
      `lakatos: the program does not type check; reporting ${n} annotation${n === 1 ? "" : "s"} as InputError`,
    );
    emitEnvelope({ ...base, annotations });
    return 2;
  }
  rejectUnreadableFormulas(files);
  const runDir = claimRunDir(base.startedAt);
  const plan = spine.plan(files, runDir);
  noteUnsupportedRanges(plan.untried);
  const meta = { ...base, ...plan.meta };

  if (plan.outFiles.length === 0 || spine.run === undefined) {
    emitEnvelope({
      ...meta,
      ...plan.emptyMeta,
      annotations: [...plan.untried, ...plan.inputErrors],
    });
    return plan.inputErrors.length > 0 ? 2 : plan.emptyExit;
  }

  // The guard spans the engine's run and the report that follows. The run
  // is the window in which lakatos can still learn of a signal — from the
  // child's death — and the report is the one in which a second signal
  // must not cut the envelope short: Ctrl-C is rarely pressed just once,
  // and the first one lands while the engine is still dying.
  const run = spine.run;
  return withInterruptGuard(() => {
    const outcome = run(plan, runDir);
    if (outcome.kind === "interrupted") {
      const n = plan.identities.length;
      console.error(
        `lakatos: interrupted by ${outcome.signal}; reporting ${n} annotation${n === 1 ? "" : "s"} as User`,
      );
      return stoppedExit(
        meta,
        plan,
        interruptedResults(plan.identities, outcome.signal),
      );
    }
    if (outcome.kind === "unhealthy") {
      for (const m of outcome.messages) console.error(`error: ${m}`);
      return stoppedExit(
        meta,
        plan,
        plan.identities.map((i) => ({ ...i, szs: "NotTried" as const })),
      );
    }

    emitEnvelope({
      ...meta,
      ...outcome.meta,
      annotations: [
        ...outcome.annotations,
        ...plan.untried,
        ...plan.inputErrors,
      ],
    });
    // Bad input and engine failures outrank a refutation: the documented
    // exit-2 error mode, even alongside healthy verdicts.
    if (plan.inputErrors.length > 0 || outcome.degraded) return 2;
    return outcome.refuted ? 1 : 0;
  });
}

const USAGE =
  "usage: lakatos <prove|refute|check> [--seed <n>] [files-or-globs...]";

const HELP = `${USAGE}

commands:
  prove   emit Lean for each file and attempt a proof per annotation;
          artifacts land in .lakatos/<run>/thales/ (requires the Lean
          toolchain)
  refute  generate property tests from @ensures annotations, run them, and
          print a JSON report to stdout
  check   prove and refute combined (not implemented yet)

when no files are given, lakatos discovers your sources: the files that
tsconfig.json would compile or, failing that, src/**. declaration files
(.d.ts) are skipped unless a pattern names them.

when tsconfig.json is present, lakatos type checks the whole project first
and refuses to analyze a program that does not compile (annotations report
InputError; without a tsconfig the run proceeds unchecked, with a warning).

options:
  --seed <n>  reproduce a prior refute run's generation (echoed in the report)
  -h, --help  show this help`;

const COMMANDS = ["prove", "refute", "check"] as const;
type Command = (typeof COMMANDS)[number];

export function main(argv: string[] = process.argv.slice(2)): number {
  // parseArgs throws on unknown options and the like — usage errors, which
  // map to the documented exit-2 mode; anything else crashes loudly.
  let positionals: string[];
  let values: { seed?: string; help?: boolean };
  try {
    ({ positionals, values } = parseArgs({
      args: argv,
      allowPositionals: true,
      options: {
        seed: { type: "string" },
        help: { type: "boolean", short: "h" },
      },
    }));
  } catch (e) {
    if (
      e instanceof TypeError &&
      "code" in e &&
      typeof e.code === "string" &&
      e.code.startsWith("ERR_PARSE_ARGS_")
    ) {
      console.error(USAGE);
      return 2;
    }
    throw e;
  }
  if (values.help) {
    console.log(HELP);
    return 0;
  }
  const command = positionals[0];
  const patterns = positionals.slice(1);
  if (!COMMANDS.includes(command as Command)) {
    console.error(USAGE);
    return 2;
  }
  // User-facing errors below — a bad --seed, file resolution coming up
  // empty, a malformed tsconfig, compile errors — are LemmaErrors and map
  // to the documented exit-2 error mode; anything else is an internal bug
  // and crashes loudly.
  try {
    // The seed is parsed before anything else so a bad one is reported
    // without first resolving files.
    const spine =
      command === "refute"
        ? refuteSpine(
            values.seed !== undefined ? parseSeed(values.seed) : randomSeed(),
          )
        : command === "prove"
          ? plainProveSpine()
          : stubSpine(command as Command);
    return runCommand(spine, patterns);
  } catch (e) {
    if (e instanceof LemmaError) {
      console.error(`error: ${e.message}`);
      return 2;
    }
    throw e;
  }
}

function resolve(patterns: string[]): string[] {
  const { files, source } = resolveFiles(patterns);
  if (source !== "arguments") {
    console.error(
      `lakatos: no files given; discovered ${files.length} file(s) via ${source}`,
    );
  }
  return files;
}

/** Reject a formula lemma's parsers cannot read before any engine runs: a
 * parse-level reject is a compile error whichever command asked, so every
 * command aborts on the same diagnostic. A clamp-emptied interval parses;
 * the engines contain it per annotation. */
function rejectUnreadableFormulas(files: string[]): void {
  for (const file of files) {
    for (const a of extract(file).annotations) {
      try {
        parseBody(parsePrefix(a.formula).body);
      } catch (e) {
        if (e instanceof EmptyAfterClampError) continue;
        if (e instanceof LemmaError)
          throw new LemmaError(
            `${file}:${a.line}: @ensures{${a.propertyName}}: ${e.message}`,
            { cause: e },
          );
        throw e;
      }
    }
  }
}

/** The engine-independent enumeration: every annotation lemma can extract
 * and parse, plus the extraction-level input errors beside it. A formula
 * lemma itself cannot read is a compile error whichever command asked. */
function enumerate(files: string[]): {
  identities: PropertyIdentity[];
  invalid: { file: string; invalid: InvalidAnnotation[] }[];
} {
  const identities: PropertyIdentity[] = [];
  const invalid: { file: string; invalid: InvalidAnnotation[] }[] = [];
  for (const file of files) {
    const extracted = extract(file);
    invalid.push({ file, invalid: extracted.invalid });
    for (const a of extracted.annotations) {
      try {
        parseBody(parsePrefix(a.formula).body);
      } catch (e) {
        if (e instanceof LemmaError)
          throw new LemmaError(
            `${file}:${a.line}: @ensures{${a.propertyName}}: ${e.message}`,
            { cause: e },
          );
        throw e;
      }
      identities.push({
        file,
        function: qualifiedName(a.functionName, a.className, a.isStatic),
        property: a.propertyName,
      });
    }
  }
  return { identities, invalid };
}

function refuteSpine(seed: number): Spine {
  return {
    plan(files, runDir) {
      const outRoot = path.join(runDir, "pabst");
      const results = generate(files, outRoot, seed);
      const identities: PropertyIdentity[] = results.flatMap((r) =>
        r.properties.map((p) => ({ file: r.sourceFile, ...p })),
      );
      const inputErrors = inputErrorResults(
        results.map((r) => ({ file: r.sourceFile, invalid: r.invalid })),
      );
      const generated = identities.length;
      console.error(
        `lakatos: generated ${generated} propert${generated === 1 ? "y" : "ies"} across ${results.length} file(s) into ${outRoot}/`,
      );
      // Scope the run to the out-files generated by THIS invocation, not the
      // whole directory: an empty file list would tell vitest to run
      // everything, so the runner short-circuits when nothing was generated.
      return {
        identities,
        untried: results.flatMap((r) =>
          r.untried.map((u) => ({
            file: r.sourceFile,
            function: u.function,
            property: u.property,
            szs: "NotTried" as const,
            kind: "unsupported-range" as const,
            reason: u.reason,
          })),
        ),
        inputErrors,
        outFiles: results.flatMap((r) =>
          r.outFile !== undefined ? [r.outFile] : [],
        ),
        meta: { seed, generated },
        emptyMeta: { passed: 0, failed: 0 },
        emptyExit: 0,
      };
    },

    run(plan, runDir) {
      const result = runTests(
        plan.outFiles,
        path.join(runDir, "pabst", "vitest-results.json"),
      );
      if (result.kind === "interrupted")
        return { kind: "interrupted", signal: result.signal };
      // Unhealthy runs (vitest died before reporting, or the generated suite
      // failed to load) still honor the output contract: diagnostics on
      // stderr, a NotTried envelope on stdout, and the documented exit 2,
      // not vitest's raw status.
      if (result.kind !== "completed") {
        if (result.kind === "no-results") {
          process.stderr.write(result.stdout);
          process.stderr.write(result.stderr);
          return { kind: "unhealthy", messages: [] };
        }
        return { kind: "unhealthy", messages: result.messages };
      }
      const join = joinRefuteVerdicts(plan.identities, result.json);
      // A failure the join cannot read means the reporter never ran; that is
      // engine breakage, contained like a run that reported nothing at all.
      if (join.kind === "unreadable")
        return { kind: "unhealthy", messages: join.messages };
      const failed = result.json.numFailedTests;
      return {
        kind: "completed",
        annotations: join.annotations,
        meta: { passed: result.json.numPassedTests, failed },
        degraded: false,
        // A failing test is a refutation whatever kind of issue it carried:
        // the count, not the SZS status, is what the exit code reports.
        refuted: failed > 0,
      };
    },
  };
}

/** Shared by both prove spines: containment, join, and health discipline
 * over a Lean run result, whatever produced the artifacts. */
function leanRunOutcome(
  result: LeanRunResult,
  plan: Plan,
  sourceOf: Map<string, string>,
): Outcome {
  if (result.kind === "interrupted")
    return { kind: "interrupted", signal: result.signal };
  if (result.kind === "no-project")
    return { kind: "unhealthy", messages: [result.message] };
  if (result.kind === "failed") {
    process.stderr.write(result.stdout);
    process.stderr.write(result.stderr);
    return {
      kind: "unhealthy",
      messages: ["the Lean run failed before reporting verdicts"],
    };
  }
  for (const d of result.diagnostics) console.error(d);
  for (const f of result.failures)
    for (const m of f.messages) console.error(`error: ${m}`);

  // A contained per-artifact failure degrades only that file's
  // annotations; every healthy verdict still reaches the envelope.
  const failedSources = new Set(
    result.failures.map((f) => sourceOf.get(f.file)),
  );
  const failedResults: AnnotationResult[] = plan.identities
    .filter((i) => failedSources.has(i.file))
    .map((i) => ({
      ...i,
      szs: "Error" as const,
      error:
        "the Lean run on this file's artifact failed before reporting its verdicts",
    }));
  const join = joinProveVerdicts(
    plan.identities.filter((i) => !failedSources.has(i.file)),
    result.verdicts,
  );
  if (join.kind === "mismatched")
    return { kind: "unhealthy", messages: join.messages };

  return {
    kind: "completed",
    annotations: [...join.annotations, ...failedResults],
    meta: {},
    degraded: result.failures.length > 0,
    refuted: join.annotations.some((a) => a.szs === "CounterSatisfiable"),
  };
}

/** The plain-Lean emission spine: the frontend classifies everything it
 * cannot map before emission, thales-emit renders the artifacts, and the
 * shared Lean-run discipline does the rest. */
function plainProveSpine(): Spine {
  const sourceOf = new Map<string, string>();
  const jsonOf = new Map<string, string>();
  return {
    plan(files, runDir) {
      const outRoot = path.join(runDir, "thales");
      const artifacts = writeEmissionArtifacts(files, outRoot);
      const inputErrors = inputErrorResults(
        artifacts.map((a) => ({ file: a.sourceFile, invalid: a.invalid })),
      );
      // Partition each file's annotations once, by object identity:
      // classified ones were settled by the frontend and are never
      // expected in the verdict join; the rest are the identities the
      // join must account for.
      const tried: PropertyIdentity[] = [];
      const classifiedResults: AnnotationResult[] = [];
      const proveFiles: string[] = [];
      for (const a of artifacts) {
        const classified = new Map(a.classified.map((c) => [c.annotation, c]));
        for (const r of a.annotations) {
          const identity = {
            file: a.sourceFile,
            function: qualifiedName(r.functionName, r.className, r.isStatic),
            property: r.propertyName,
          };
          const c = classified.get(r);
          if (c === undefined) tried.push(identity);
          // The envelope's field split: an engine failure explains
          // itself in `error`, everything else in `reason`.
          else if (c.szs === "Error")
            classifiedResults.push({
              ...identity,
              szs: c.szs,
              error: c.reason,
            });
          else
            classifiedResults.push({
              ...identity,
              szs: c.szs,
              ...(c.kind !== undefined ? { kind: c.kind } : {}),
              reason: c.reason,
            });
        }
        if (a.leanFile !== undefined) {
          sourceOf.set(a.leanFile, a.sourceFile);
          jsonOf.set(a.leanFile, a.jsonFile!);
          proveFiles.push(a.leanFile);
        }
      }
      const n = tried.length;
      console.error(
        `lakatos: emitted ${n} annotation${n === 1 ? "" : "s"} across ${artifacts.length} file(s) into ${outRoot}/`,
      );
      return {
        identities: tried,
        untried: classifiedResults,
        inputErrors,
        outFiles: proveFiles,
        meta: {},
        emptyMeta: {},
        emptyExit: 0,
      };
    },

    run(plan) {
      const jobs = plan.outFiles.map((leanFile) => ({
        jsonFile: jsonOf.get(leanFile)!,
        leanFile,
      }));
      return leanRunOutcome(
        runEmission(jobs, findEngineRoot()),
        plan,
        sourceOf,
      );
    },
  };
}

/** A command with no engine yet: it enumerates what it would have attempted
 * and reports every annotation NotTried. */
function stubSpine(command: Command): Spine {
  return {
    plan(files) {
      const { identities, invalid } = enumerate(files);
      const inputErrors = inputErrorResults(invalid);
      console.error(`lakatos: ${command} is not implemented yet`);
      return {
        identities: [],
        untried: identities.map((i) => ({ ...i, szs: "NotTried" as const })),
        inputErrors,
        outFiles: [],
        meta: {},
        emptyMeta: {},
        emptyExit: 1,
      };
    },
  };
}

// npm installs the bin as a symlink (node_modules/.bin/lakatos -> this
// file). Node resolves the main module to its realpath, but argv[1] keeps
// the symlink path, so argv[1] must be realpath'd before comparing.
if (
  process.argv[1] &&
  import.meta.url === pathToFileURL(realpathSync(process.argv[1])).href
) {
  process.exit(main());
}
