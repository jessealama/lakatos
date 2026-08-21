#!/usr/bin/env node
import { parseArgs } from "node:util";
import { existsSync, readFileSync, realpathSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { writeArtifacts } from "../engines/thales/frontend/src/artifacts.js";
import { findEngineRoot, runLean } from "../engines/thales/frontend/src/run.js";
import { generate } from "../engines/pabst/src/codegen.js";
import { runTests } from "../engines/pabst/src/run.js";
import { parseSeed, randomSeed } from "../engines/pabst/src/seed.js";
import { resolveFiles } from "../lemma/src/discover.js";
import { LemmaError } from "../lemma/src/errors.js";
import { qualifiedName } from "../lemma/src/qualified-name.js";
import { extract, type InvalidAnnotation } from "../lemma/src/extract.js";
import { parsePrefix } from "../lemma/src/prefix-parser.js";
import { parseBody } from "../lemma/src/formula-parser.js";
import {
  joinProveVerdicts,
  joinRefuteVerdicts,
  type AnnotationResult,
  type Envelope,
  type PropertyIdentity,
} from "./envelope.js";

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

/** The unhealthy-run output contract shared by refute and prove: a
 * NotTried envelope on stdout (annotations were produced but never
 * evaluated) and the documented exit 2. */
function notTriedExit(
  meta: EnvelopeMeta,
  identities: PropertyIdentity[],
  inputErrors: AnnotationResult[],
  untried: AnnotationResult[] = [],
): number {
  emitEnvelope({
    ...meta,
    annotations: [
      ...identities.map((i) => ({ ...i, szs: "NotTried" as const })),
      ...untried,
      ...inputErrors,
    ],
  });
  return 2;
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
      kind: "completed";
      annotations: AnnotationResult[];
      meta: Partial<EnvelopeMeta>;
      /** The engine failed on part of the run: exit 2 beside the verdicts. */
      degraded: boolean;
      /** The engine refuted something: the documented exit 1. */
      refuted: boolean;
    };

interface Spine {
  plan(files: string[]): Plan;
  /** Absent for a command with no engine — its plan yields no artifacts. */
  run?(plan: Plan): Outcome;
}

/** The pipeline every command shares: resolve files, capture run meta, run
 * the engine's codegen, and turn its outcome into one envelope and one exit
 * code. Only the codegen, the run, the verdict join, and the two exit-code
 * contributions are engine-specific. */
function runCommand(spine: Spine, patterns: string[]): number {
  const files = resolve(patterns);
  const base = captureMeta();
  const plan = spine.plan(files);
  const meta = { ...base, ...plan.meta };

  if (plan.outFiles.length === 0 || spine.run === undefined) {
    emitEnvelope({
      ...meta,
      ...plan.emptyMeta,
      annotations: [...plan.untried, ...plan.inputErrors],
    });
    return plan.inputErrors.length > 0 ? 2 : plan.emptyExit;
  }

  const outcome = spine.run(plan);
  if (outcome.kind === "unhealthy") {
    for (const m of outcome.messages) console.error(`error: ${m}`);
    return notTriedExit(meta, plan.identities, plan.inputErrors, plan.untried);
  }

  emitEnvelope({
    ...meta,
    ...outcome.meta,
    annotations: [...outcome.annotations, ...plan.untried, ...plan.inputErrors],
  });
  // Bad input and engine failures outrank a refutation: the documented
  // exit-2 error mode, even alongside healthy verdicts.
  if (plan.inputErrors.length > 0 || outcome.degraded) return 2;
  return outcome.refuted ? 1 : 0;
}

const USAGE =
  "usage: lakatos <prove|refute|check> [--seed <n>] [files-or-globs...]";

const HELP = `${USAGE}

commands:
  prove   transcribe each file to Lean and attempt a proof per annotation;
          artifacts land in .thales/ (requires the Lean toolchain)
  refute  generate property tests from @ensures annotations, run them, and
          print a JSON report to stdout
  check   prove and refute combined (not implemented yet)

when no files are given, lakatos discovers your sources: the files that
tsconfig.json would compile or, failing that, src/**. declaration files
(.d.ts) are skipped unless a pattern names them.

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
          ? proveSpine()
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
    plan(files) {
      const results = generate(files, ".pabst", seed);
      const identities: PropertyIdentity[] = results.flatMap((r) =>
        r.properties.map((p) => ({ file: r.sourceFile, ...p })),
      );
      const inputErrors = inputErrorResults(
        results.map((r) => ({ file: r.sourceFile, invalid: r.invalid })),
      );
      const generated = identities.length;
      console.error(
        `lakatos: generated ${generated} propert${generated === 1 ? "y" : "ies"} across ${results.length} file(s) into .pabst/`,
      );
      // Scope the run to the out-files generated by THIS invocation: .pabst/
      // accumulates mirrors from earlier runs, and running the whole directory
      // would re-execute them and mix their issues into this envelope. With
      // nothing generated there is nothing to run — and an empty file list
      // would tell vitest to run everything, so the runner short-circuits.
      return {
        identities,
        untried: [],
        inputErrors,
        outFiles: results.flatMap((r) =>
          r.outFile !== undefined ? [r.outFile] : [],
        ),
        meta: { seed, generated },
        emptyMeta: { passed: 0, failed: 0 },
        emptyExit: 0,
      };
    },

    run(plan) {
      const result = runTests(plan.outFiles);
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
      const failed = result.json.numFailedTests;
      return {
        kind: "completed",
        annotations: joinRefuteVerdicts(plan.identities, result.json),
        meta: { passed: result.json.numPassedTests, failed },
        degraded: false,
        // A failing test is a refutation whatever kind of issue it carried:
        // the count, not the SZS status, is what the exit code reports.
        refuted: failed > 0,
      };
    },
  };
}

function proveSpine(): Spine {
  // The transcriber's per-artifact source mapping, needed by the run to
  // attribute a failed artifact back to the file its annotations came from.
  const sourceOf = new Map<string, string>();
  return {
    plan(files) {
      const artifacts = writeArtifacts(files);
      const inputErrors = inputErrorResults(
        artifacts.map((a) => ({ file: a.sourceFile, invalid: a.invalid })),
      );
      // Partition each artifact's annotations once, by object identity:
      // untried ones (the transcriber emitted no prove command) become
      // NotTried entries here and are never expected in the verdict join;
      // the rest are the identities the join must account for. An artifact
      // with no prove command at all has nothing for Lean to report.
      const tried: PropertyIdentity[] = [];
      const untriedResults: AnnotationResult[] = [];
      const proveFiles: string[] = [];
      for (const a of artifacts) {
        const untried = new Map(a.untried.map((u) => [u.annotation, u]));
        for (const r of a.annotations) {
          const identity = {
            file: a.sourceFile,
            function: qualifiedName(r.functionName, r.className, r.isStatic),
            property: r.propertyName,
          };
          const u = untried.get(r);
          if (u === undefined) tried.push(identity);
          else
            untriedResults.push({
              ...identity,
              szs: "NotTried",
              kind: u.kind,
              reason: u.reason,
            });
        }
        if (a.outFile !== undefined) sourceOf.set(a.outFile, a.sourceFile);
        if (a.outFile !== undefined && a.annotations.length > untried.size)
          proveFiles.push(a.outFile);
      }
      const n = tried.length;
      console.error(
        `lakatos: transcribed ${n} annotation${n === 1 ? "" : "s"} across ${artifacts.length} file(s) into .thales/`,
      );
      const m = untriedResults.length;
      if (m > 0)
        console.error(
          `lakatos: ${m} annotation${m === 1 ? "" : "s"} not tried (unsupported range)`,
        );
      return {
        identities: tried,
        untried: untriedResults,
        inputErrors,
        outFiles: proveFiles,
        meta: {},
        emptyMeta: {},
        emptyExit: 0,
      };
    },

    run(plan) {
      const result = runLean(plan.outFiles, findEngineRoot());
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
