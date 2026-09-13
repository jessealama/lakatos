#!/usr/bin/env node
// `tarski-test262`: run a slice of test262 against the evaluator.
//
//   tarski-test262 setup [--pin <pin.json>]
//   tarski-test262 test/harness [--check test262/expected.json]
//
// A slice is a directory or a file under the checkout. Every test is
// planned (`plan.ts`), run once against the binary (`run.ts`), and
// counted into a per-directory table (`report.ts`). `--check` compares
// the table against a committed expectations file and exits 1 on any
// difference, in either direction: the table is a ratchet, so a count
// that improved has to be written down before it can be relied on.

import {
  existsSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { HarnessError, listTests, planTest, type Plan } from "./plan.js";
import {
  defaultBinary,
  defaultCheckout,
  findTarskiRoot,
  pinPath,
} from "./paths.js";
import {
  diffExpectations,
  renderDetails,
  renderTable,
  tabulate,
  type Expectations,
  type Result,
} from "./report.js";
import { runOne, type Outcome } from "./run.js";
import { setupTest262, type Pin } from "./setup.js";

/** What the command line asked for. */
interface Options {
  slices: string[];
  test262?: string;
  binary?: string;
  timeout: number;
  check?: string;
  write?: string;
}

/** A usage error, reported and exited 2 rather than thrown out of `main`. */
class UsageError extends Error {}

const FLAGS = [
  "--test262",
  "--binary",
  "--timeout",
  "--check",
  "--write",
] as const;

function parseArgs(argv: readonly string[]): Options {
  const options: Options = { slices: [], timeout: 10_000 };
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i] ?? "";
    if (!arg.startsWith("--")) {
      options.slices.push(arg);
      continue;
    }
    if (!(FLAGS as readonly string[]).includes(arg))
      throw new UsageError(`unknown flag ${arg}`);
    const value = argv[i + 1];
    if (value === undefined) throw new UsageError(`${arg} needs a value`);
    i++;
    if (arg === "--test262") options.test262 = value;
    else if (arg === "--binary") options.binary = value;
    else if (arg === "--check") options.check = value;
    else if (arg === "--write") options.write = value;
    else {
      const ms = Number(value);
      if (!Number.isInteger(ms) || ms <= 0)
        throw new UsageError(`--timeout needs a positive integer`);
      options.timeout = ms;
    }
  }
  if (options.slices.length === 0)
    throw new UsageError("at least one slice is needed");
  return options;
}

/** Plan and run every test under the slices, in order. */
function runSlices(
  checkout: string,
  binary: string,
  slices: readonly string[],
  timeout: number,
  scratch: string,
): Result[] {
  const readHarness = (name: string): string => {
    try {
      return readFileSync(path.join(checkout, "harness", name), "utf8");
    } catch {
      throw new HarnessError(`no harness file ${name}`);
    }
  };
  const results: Result[] = [];
  for (const relative of listTests(checkout, slices)) {
    const directory = path.dirname(relative).split(path.sep).join("/");
    let plan: Plan;
    try {
      plan = planTest(
        relative,
        readFileSync(path.join(checkout, relative), "utf8"),
        readHarness,
      );
    } catch (e) {
      // A missing include is the runner's own machinery, and the test
      // still gets a row: silence would make the slice look smaller.
      results.push({
        path: relative,
        directory,
        plan: { kind: "run", source: "" },
        outcome: { class: "harness-error", detail: (e as Error).message },
      });
      continue;
    }
    const outcome: Outcome | undefined =
      plan.kind === "run" ? runOne(plan, binary, timeout, scratch) : undefined;
    results.push({
      path: relative,
      directory,
      plan,
      ...(outcome === undefined ? {} : { outcome }),
    });
  }
  return results;
}

/** `--write`'s serialisation: prettier-clean, so the file can be committed. */
function serialise(directories: Expectations["directories"]): string {
  return `${JSON.stringify({ directories }, null, 2)}\n`;
}

function readPin(file: string): Pin {
  return JSON.parse(readFileSync(file, "utf8")) as Pin;
}

export function main(argv: readonly string[]): number {
  const root = findTarskiRoot();
  if (root === undefined) {
    console.error("tarski-test262: no tarski package here");
    return 2;
  }
  if (argv[0] === "setup") {
    // `--pin` names another pin file. The committed one is the default
    // and what CI uses; the flag is how the suite points `setup` at a
    // scratch repository instead of fetching tc39/test262 over the
    // network.
    const pin =
      argv[1] === "--pin" && argv[2] !== undefined ? argv[2] : undefined;
    if (argv.length > (pin === undefined ? 1 : 3)) {
      console.error("usage: tarski-test262 setup [--pin <pin.json>]");
      return 2;
    }
    setupTest262(defaultCheckout(root), readPin(pin ?? pinPath(root)), (line) =>
      console.log(line),
    );
    return 0;
  }

  let options: Options;
  try {
    options = parseArgs(argv);
  } catch (e) {
    console.error(`tarski-test262: ${(e as UsageError).message}`);
    console.error(
      "usage: tarski-test262 <slice>... [--test262 <dir>] [--binary <path>]",
    );
    console.error(
      "       [--timeout <ms>] [--check <expected.json>] [--write <expected.json>]",
    );
    return 2;
  }

  const checkout = options.test262 ?? defaultCheckout(root);
  if (!existsSync(path.join(checkout, "harness", "sta.js"))) {
    console.error(`tarski-test262: no test262 checkout at ${checkout}`);
    console.error(
      "run `node tarski/scripts/setup-test262.js`, or set LAKATOS_TEST262",
    );
    return 2;
  }
  const binary = options.binary ?? defaultBinary(root);
  if (!existsSync(binary)) {
    console.error(`tarski-test262: no evaluator at ${binary}`);
    console.error("run `lake build tarski` in tarski/");
    return 2;
  }

  const scratch = mkdtempSync(path.join(tmpdir(), "tarski-test262-"));
  let results: Result[];
  try {
    results = runSlices(
      checkout,
      binary,
      options.slices,
      options.timeout,
      scratch,
    );
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }

  const counts = tabulate(results);
  console.log(renderTable(counts));
  const details = renderDetails(results);
  if (details.length > 0) console.log(details);

  if (options.write !== undefined) {
    writeFileSync(options.write, serialise(counts));
    console.log(`wrote ${options.write}`);
  }
  if (options.check !== undefined) {
    const expected = JSON.parse(
      readFileSync(options.check, "utf8"),
    ) as Expectations;
    const diff = diffExpectations(counts, expected.directories);
    if (diff.length > 0) {
      for (const line of diff) console.error(line);
      return 1;
    }
    console.log(`expectations match ${options.check}`);
  }
  return 0;
}

// npm may install this behind a symlink, and Node resolves the main
// module to its realpath while argv[1] keeps the link.
/* v8 ignore start -- true only when node runs this file, which the
   suite does out of process, where this process's counters cannot see
   it. */
if (
  process.argv[1] &&
  import.meta.url === pathToFileURL(realpathSync(process.argv[1])).href
) {
  process.exit(main(process.argv.slice(2)));
}
/* v8 ignore stop */
