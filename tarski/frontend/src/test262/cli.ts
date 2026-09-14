#!/usr/bin/env node
// `tarski-test262`: run a slice of test262 against the evaluator.
//
//   tarski-test262 setup [--pin <pin.json>]
//   tarski-test262 test/harness [--check test262/expected.json]
//   tarski-test262 test/language --summary --markdown results.md
//
// A slice is a directory or a file under the checkout. Every test is
// planned (`plan.ts`), run once against the binary (`run.ts`), and
// counted into a per-directory table (`report.ts`). `--check` compares
// the table against a committed expectations file and exits 1 on any
// difference, in either direction: the table is a ratchet, so a count
// that improved has to be written down before it can be relied on.
//
// `--markdown` and `--json` write the committed results files of the
// scheduled whole-suite run, rolled up to three path components; `--budget`
// bounds that run's wall clock, the tests past it counted as not run for
// `budget` rather than dropped; `--summary` trades the per-test lists for
// a line of progress per directory group on stderr.

import { execFileSync } from "node:child_process";
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
  groupKey,
  renderDetails,
  renderJson,
  renderMarkdown,
  renderTable,
  summarise,
  tabulate,
  type Disposition,
  type Expectations,
  type Result,
} from "./report.js";
import { runOne, type Outcome } from "./run.js";
import { headOf, setupTest262, type Exec, type Pin } from "./setup.js";

/** What the command line asked for. */
interface Options {
  slices: string[];
  test262?: string;
  binary?: string;
  timeout: number;
  budget: number;
  summary: boolean;
  check?: string;
  write?: string;
  markdown?: string;
  json?: string;
}

/** A usage error, reported and exited 2 rather than thrown out of `main`. */
class UsageError extends Error {}

const FLAGS = [
  "--test262",
  "--binary",
  "--timeout",
  "--budget",
  "--check",
  "--write",
  "--markdown",
  "--json",
] as const;

function parseArgs(argv: readonly string[]): Options {
  const options: Options = {
    slices: [],
    timeout: 10_000,
    // No budget until one is asked for: a slice small enough to name by
    // hand is one nobody wants truncated.
    budget: Infinity,
    summary: false,
  };
  for (let i = 0; i < argv.length; i++) {
    /* v8 ignore next -- `i` is an index into `argv`. */
    const arg = argv[i] ?? "";
    if (!arg.startsWith("--")) {
      options.slices.push(arg);
      continue;
    }
    if (arg === "--summary") {
      options.summary = true;
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
    else if (arg === "--markdown") options.markdown = value;
    else if (arg === "--json") options.json = value;
    else if (arg === "--budget") {
      const ms = Number(value);
      // Zero is allowed, and means every planned run is `budget`: the one
      // setting under which the arm can be exercised without a clock.
      if (!Number.isInteger(ms) || ms < 0)
        throw new UsageError(`--budget needs a non-negative integer`);
      options.budget = ms;
    } else {
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

/**
 * Plan and run every test under the slices, in order. `budgetMs` bounds
 * the whole loop's wall clock: once it is spent every remaining test is
 * planned and listed but not spawned, counted as not run for `budget`, so
 * a truncated run says so in its own table instead of shrinking. `onGroup`
 * is called once per depth-three directory group, with the tests finished
 * so far — a job that prints nothing for an hour is one nobody can tell
 * from a hung one.
 */
function runSlices(
  checkout: string,
  binary: string,
  slices: readonly string[],
  timeout: number,
  scratch: string,
  budgetMs: number,
  onGroup?: (done: number, total: number, group: string) => void,
): Result[] {
  const readHarness = (name: string): string => {
    try {
      return readFileSync(path.join(checkout, "harness", name), "utf8");
    } catch {
      throw new HarnessError(`no harness file ${name}`);
    }
  };
  const started = Date.now();
  const tests = listTests(checkout, slices);
  const results: Result[] = [];
  let group: string | undefined;
  let done = 0;
  const report = (): void => {
    if (group !== undefined) onGroup?.(done, tests.length, group);
  };
  for (const relative of tests) {
    const directory = path.dirname(relative).split(path.sep).join("/");
    const next = groupKey(directory);
    if (next !== group) {
      report();
      group = next;
    }
    done++;
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
        plan: { kind: "run" },
        outcome: { class: "harness-error", detail: (e as Error).message },
      });
      continue;
    }
    // A result never holds its source: the whole suite is tens of
    // thousands of results, and each assembled document is tens of
    // kilobytes.
    const disposition: Disposition =
      plan.kind === "run"
        ? { kind: "run", ...(plan.negative ? { negative: plan.negative } : {}) }
        : plan;
    if (plan.kind === "run" && Date.now() - started >= budgetMs) {
      results.push({
        path: relative,
        directory,
        plan: { kind: "not-run", reason: "budget" },
      });
      continue;
    }
    const outcome: Outcome | undefined =
      plan.kind === "run" ? runOne(plan, binary, timeout, scratch) : undefined;
    results.push({
      path: relative,
      directory,
      plan: disposition,
      ...(outcome === undefined ? {} : { outcome }),
    });
  }
  report();
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
  /* v8 ignore start -- true only for a copy of this file outside any
     lakatos checkout or installation, which the suite cannot arrange
     from inside one. `paths.test.ts` covers the walk's own answer. */
  if (root === undefined) {
    console.error("tarski-test262: no tarski package here");
    return 2;
  }
  /* v8 ignore stop */
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
    /* v8 ignore next 3 -- without `--pin` this reads the committed pin
       and fetches tc39/test262 over the network, which is what CI does
       and what the suite must not. */
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
    console.error("       [--timeout <ms>] [--budget <ms>] [--summary]");
    console.error("       [--check <expected.json>] [--write <expected.json>]");
    console.error("       [--markdown <file>] [--json <file>]");
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
      options.budget,
      options.summary
        ? (done, total, group): void =>
            console.error(`  ${done}/${total}  ${group}`)
        : undefined,
    );
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }

  const counts = tabulate(results);
  console.log(renderTable(counts));
  const details = renderDetails(results, { lists: !options.summary });
  if (details.length > 0) console.log(details);

  if (options.markdown !== undefined || options.json !== undefined) {
    // The table is labelled with the commit the checkout is really at, so
    // a local run against another one is honestly labelled rather than
    // refused; the mismatch is a warning, and the committed table is held
    // to the pin by the suite that reads it.
    const commit = headOf(checkout, execFileSync as Exec) ?? null;
    const pinned = readPin(pinPath(root)).commit;
    if (commit !== null && commit !== pinned)
      console.error(`test262 checkout is at ${commit}, the pin is ${pinned}`);
    const summary = summarise(results, {
      commit,
      slices: options.slices,
      timeoutMs: options.timeout,
    });
    if (options.json !== undefined) {
      writeFileSync(options.json, renderJson(summary));
      console.log(`wrote ${options.json}`);
    }
    if (options.markdown !== undefined) {
      writeFileSync(options.markdown, renderMarkdown(summary));
      console.log(`wrote ${options.markdown}`);
    }
  }

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
