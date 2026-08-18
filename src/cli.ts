#!/usr/bin/env node
import { parseArgs } from "node:util";
import { existsSync, readFileSync, realpathSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { buildSpecs } from "../engines/pabst/src/build-spec.js";
import { writeArtifacts } from "../engines/thales/frontend/src/artifacts.js";
import { findEngineRoot, runLean } from "../engines/thales/frontend/src/run.js";
import { generate } from "../engines/pabst/src/codegen.js";
import { runTests } from "../engines/pabst/src/run.js";
import { parseSeed, randomSeed } from "../engines/pabst/src/seed.js";
import { resolveFiles } from "../lemma/src/discover.js";
import { LemmaError } from "../lemma/src/errors.js";
import { qualifiedName } from "../lemma/src/qualified-name.js";
import type { InvalidAnnotation } from "../lemma/src/extract.js";
import {
  buildEnvelope,
  joinProveVerdicts,
  notTriedEnvelope,
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
    return command === "refute"
      ? refute(patterns, values.seed)
      : command === "prove"
        ? prove(patterns)
        : notTried("check", patterns);
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

function refute(patterns: string[], seedArg: string | undefined): number {
  const seed = seedArg !== undefined ? parseSeed(seedArg) : randomSeed();
  const files = resolve(patterns);
  const startedAt = new Date().toISOString();
  const cwd = process.cwd();
  const version = readVersion();

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

  const meta = { version, startedAt, cwd, seed, generated };

  // Scope the run to the out-files generated by THIS invocation: .pabst/
  // accumulates mirrors from earlier runs, and running the whole directory
  // would re-execute them and mix their issues into this envelope. With
  // nothing generated there is nothing to run — and an empty file list
  // would tell vitest to run everything, so short-circuit instead.
  const outFiles = results.flatMap((r) =>
    r.outFile !== undefined ? [r.outFile] : [],
  );
  if (outFiles.length === 0) {
    console.log(
      JSON.stringify(
        { ...meta, passed: 0, failed: 0, annotations: inputErrors },
        null,
        2,
      ),
    );
    return inputErrors.length > 0 ? 2 : 0;
  }

  const result = runTests(outFiles);

  // Unhealthy runs (vitest died before reporting, or the generated suite
  // failed to load) still honor the output contract: diagnostics on stderr,
  // a NotTried envelope on stdout — the annotations were generated but
  // never evaluated — and the documented exit 2, not vitest's raw status.
  if (result.kind !== "completed") {
    if (result.kind === "no-results") {
      process.stderr.write(result.stdout);
      process.stderr.write(result.stderr);
    } else {
      for (const m of result.messages) console.error(`error: ${m}`);
    }
    console.log(
      JSON.stringify(
        {
          ...meta,
          annotations: [
            ...identities.map((i) => ({ ...i, szs: "NotTried" })),
            ...inputErrors,
          ],
        },
        null,
        2,
      ),
    );
    return 2;
  }

  const envelope = buildEnvelope(meta, result.json, identities);
  envelope.annotations.push(...inputErrors);
  console.log(JSON.stringify(envelope, null, 2));
  // Bad input outranks a refutation: exit 2 even when counterexamples were
  // found, so malformed annotations are never mistaken for a clean 0/1 run.
  if (inputErrors.length > 0) return 2;
  return (envelope.failed ?? 0) > 0 ? 1 : 0;
}

function prove(patterns: string[]): number {
  const files = resolve(patterns);
  const startedAt = new Date().toISOString();
  const cwd = process.cwd();
  const version = readVersion();

  const artifacts = writeArtifacts(files);
  const identities: PropertyIdentity[] = artifacts.flatMap((a) =>
    a.annotations.map((r) => ({
      file: a.sourceFile,
      function: qualifiedName(r.functionName, r.className, r.isStatic),
      property: r.propertyName,
    })),
  );
  const inputErrors = inputErrorResults(
    artifacts.map((a) => ({ file: a.sourceFile, invalid: a.invalid })),
  );
  const n = identities.length;
  console.error(
    `lakatos: transcribed ${n} annotation${n === 1 ? "" : "s"} across ${artifacts.length} file(s) into .thales/`,
  );
  const meta = { version, startedAt, cwd };

  // Unhealthy runs honor the output contract: diagnostics on stderr, a
  // NotTried envelope on stdout, and the documented exit 2.
  const unhealthy = (messages: string[]): number => {
    for (const m of messages) console.error(`error: ${m}`);
    const envelope: Envelope = {
      ...meta,
      annotations: [
        ...identities.map((i) => ({ ...i, szs: "NotTried" as const })),
        ...inputErrors,
      ],
    };
    console.log(JSON.stringify(envelope, null, 2));
    return 2;
  };

  const outFiles = artifacts.flatMap((a) =>
    a.outFile !== undefined ? [a.outFile] : [],
  );
  if (outFiles.length === 0) {
    console.log(JSON.stringify({ ...meta, annotations: inputErrors }, null, 2));
    return inputErrors.length > 0 ? 2 : 0;
  }

  const result = runLean(outFiles, findEngineRoot());
  if (result.kind === "no-project") return unhealthy([result.message]);
  if (result.kind === "failed") {
    process.stderr.write(result.stdout);
    process.stderr.write(result.stderr);
    return unhealthy(["the Lean run failed before reporting verdicts"]);
  }
  for (const d of result.diagnostics) console.error(d);
  for (const f of result.failures)
    for (const m of f.messages) console.error(`error: ${m}`);

  // A contained per-artifact failure degrades only that file's
  // annotations; every healthy verdict still reaches the envelope.
  const sourceOf = new Map(
    artifacts.flatMap((a) =>
      a.outFile !== undefined ? [[a.outFile, a.sourceFile] as const] : [],
    ),
  );
  const failedSources = new Set(
    result.failures.map((f) => sourceOf.get(f.file)),
  );
  const failedResults: AnnotationResult[] = identities
    .filter((i) => failedSources.has(i.file))
    .map((i) => ({
      ...i,
      szs: "Error" as const,
      error:
        "the Lean run on this file's artifact failed before reporting its verdicts",
    }));
  const join = joinProveVerdicts(
    identities.filter((i) => !failedSources.has(i.file)),
    result.verdicts,
  );
  if (join.kind === "mismatched") return unhealthy(join.messages);

  const envelope: Envelope = {
    ...meta,
    annotations: [...join.annotations, ...failedResults, ...inputErrors],
  };
  console.log(JSON.stringify(envelope, null, 2));
  // Bad input and engine failures outrank everything: the documented
  // exit-2 error mode, even alongside healthy verdicts.
  return inputErrors.length > 0 || result.failures.length > 0 ? 2 : 0;
}

function notTried(command: Command, patterns: string[]): number {
  const files = resolve(patterns);
  const startedAt = new Date().toISOString();
  const cwd = process.cwd();
  const version = readVersion();
  const perFile = files.map((file) => ({ file, ...buildSpecs(file) }));
  const identities: PropertyIdentity[] = perFile.flatMap(({ file, specs }) =>
    specs.map((s) => ({
      file,
      function: qualifiedName(s.functionName, s.className, s.isStatic),
      property: s.name,
    })),
  );
  const inputErrors = inputErrorResults(perFile);
  console.error(`lakatos: ${command} is not implemented yet`);
  const envelope = notTriedEnvelope(version, startedAt, cwd, identities);
  envelope.annotations.push(...inputErrors);
  console.log(JSON.stringify(envelope, null, 2));
  return inputErrors.length > 0 ? 2 : 1;
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
