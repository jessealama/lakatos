// The table, the details under it, and the diff against the committed
// expectations.
//
// One row per directory, because that is the unit a slice is named by and
// the unit the expectations file pins. Skipped tests are in no row: what
// `intl402` and the parse-phase negatives amount to is a property of the
// pinned commit, not of the evaluator, so pinning their counts would make
// a test262 bump look like a regression here.

import type { NotRunReason, Plan, SkipReason } from "./plan.js";
import type { Outcome } from "./run.js";

/** The counts one directory's row carries. */
export interface DirectoryCounts {
  pass: number;
  fail: number;
  unsupported: number;
  timeout: number;
  harnessError: number;
  notRun: { noStrict: number; raw: number; async: number; module: number };
}

/** One test, planned and (unless skipped or not run) run. */
export interface Result {
  path: string;
  directory: string;
  plan: Plan;
  outcome?: Outcome;
}

/** The shape `--write` writes and `--check` reads. */
export interface Expectations {
  directories: Record<string, DirectoryCounts>;
}

const emptyCounts = (): DirectoryCounts => ({
  pass: 0,
  fail: 0,
  unsupported: 0,
  timeout: 0,
  harnessError: 0,
  notRun: { noStrict: 0, raw: 0, async: 0, module: 0 },
});

/** The four not-run reasons summed: the single column the table shows. */
const notRunTotal = (counts: DirectoryCounts): number =>
  counts.notRun.noStrict +
  counts.notRun.raw +
  counts.notRun.async +
  counts.notRun.module;

/**
 * The results as one row per directory, sorted by directory. A directory
 * whose every test was skipped has no row at all.
 */
export function tabulate(
  results: readonly Result[],
): Record<string, DirectoryCounts> {
  const rows = new Map<string, DirectoryCounts>();
  const counts = (directory: string): DirectoryCounts => {
    const existing = rows.get(directory);
    if (existing !== undefined) return existing;
    const fresh = emptyCounts();
    rows.set(directory, fresh);
    return fresh;
  };
  for (const result of results) {
    if (result.plan.kind === "skip") continue;
    if (result.plan.kind === "not-run") {
      counts(result.directory).notRun[result.plan.reason] += 1;
      continue;
    }
    const row = counts(result.directory);
    switch (result.outcome?.class) {
      case "pass":
        row.pass += 1;
        break;
      case "fail":
        row.fail += 1;
        break;
      case "unsupported":
        row.unsupported += 1;
        break;
      case "timeout":
        row.timeout += 1;
        break;
      default:
        // A planned run with no outcome cannot happen: the runner runs
        // every one. `harness-error` and the impossible case land here
        // together rather than inventing a seventh class.
        row.harnessError += 1;
    }
  }
  return Object.fromEntries(
    [...rows.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)),
  );
}

const HEADERS = [
  "directory",
  "pass",
  "fail",
  "unsupported",
  "timeout",
  "harness-error",
  "not-run",
];

/** The per-directory table, columns right-aligned under their headers. */
export function renderTable(counts: Record<string, DirectoryCounts>): string {
  const rows = Object.entries(counts).map(([directory, row]) => [
    directory,
    String(row.pass),
    String(row.fail),
    String(row.unsupported),
    String(row.timeout),
    String(row.harnessError),
    String(notRunTotal(row)),
  ]);
  const widths = HEADERS.map((header, column) =>
    Math.max(header.length, ...rows.map((row) => (row[column] ?? "").length)),
  );
  const line = (cells: readonly string[]): string =>
    cells
      .map((cell, column) =>
        // The first column is the directory, and reads as a list; every
        // other is a count, and reads as a column of digits.
        column === 0
          ? cell.padEnd(widths[column] ?? 0)
          : cell.padStart(widths[column] ?? 0),
      )
      .join("  ")
      .trimEnd();
  return [line(HEADERS), ...rows.map(line)].join("\n");
}

/** `not run:`, `skipped:`, the unsupported histogram, and the three lists. */
export function renderDetails(results: readonly Result[]): string {
  const sections: string[] = [];

  const notRun = new Map<NotRunReason, number>();
  const skipped = new Map<SkipReason, number>();
  const kinds = new Map<string, number>();
  const failures: string[] = [];
  const harnessErrors: string[] = [];
  const timeouts: string[] = [];
  const bump = <K>(counter: Map<K, number>, key: K): void => {
    counter.set(key, (counter.get(key) ?? 0) + 1);
  };

  for (const result of results) {
    if (result.plan.kind === "skip") {
      bump(skipped, result.plan.reason);
      continue;
    }
    if (result.plan.kind === "not-run") {
      bump(notRun, result.plan.reason);
      continue;
    }
    switch (result.outcome?.class) {
      case "unsupported":
        bump(kinds, result.outcome.kind);
        break;
      case "fail":
        failures.push(`  ${result.path}  ${result.outcome.detail}`);
        break;
      case "harness-error":
        harnessErrors.push(`  ${result.path}  ${result.outcome.detail}`);
        break;
      case "timeout":
        timeouts.push(`  ${result.path}`);
        break;
      default:
        break;
    }
  }

  const reasons = <K extends string>(
    title: string,
    counter: Map<K, number>,
  ): void => {
    if (counter.size === 0) return;
    sections.push(
      [
        title,
        ...[...counter.entries()].map(
          ([reason, count]) => `  ${reason}  ${count}`,
        ),
      ].join("\n"),
    );
  };
  reasons("not run:", notRun);
  reasons("skipped:", skipped);

  if (kinds.size > 0) {
    // Descending, because while the floor is what it is this histogram is
    // the actionable output: the head of it names the next slice to land.
    const histogram = [...kinds.entries()]
      .sort(([aKind, a], [bKind, b]) => b - a || (aKind < bKind ? -1 : 1))
      .map(([kind, count]) => `  ${kind}  ${count}`);
    sections.push(["unsupported:", ...histogram].join("\n"));
  }

  const list = (title: string, lines: readonly string[]): void => {
    if (lines.length > 0) sections.push([title, ...lines].join("\n"));
  };
  list("failures:", failures);
  list("harness errors:", harnessErrors);
  list("timeouts:", timeouts);

  return sections.join("\n");
}

/**
 * How the actual counts differ from the committed ones: one line per
 * directory missing from either side, and one per differing count. Empty
 * when they agree, which is what `--check` exits 0 on.
 */
export function diffExpectations(
  actual: Record<string, DirectoryCounts>,
  expected: Record<string, DirectoryCounts>,
): string[] {
  const lines: string[] = [];
  const directories = [
    ...new Set([...Object.keys(actual), ...Object.keys(expected)]),
  ].sort();
  for (const directory of directories) {
    const got = actual[directory];
    const want = expected[directory];
    if (want === undefined) {
      lines.push(`${directory}: not in the expectations`);
      continue;
    }
    if (got === undefined) {
      lines.push(`${directory}: expected but not run`);
      continue;
    }
    const compare = (
      field: string,
      gotCount: number,
      wantCount: number,
    ): void => {
      if (gotCount !== wantCount) {
        lines.push(
          `${directory}: ${field} expected ${wantCount}, got ${gotCount}`,
        );
      }
    };
    compare("pass", got.pass, want.pass);
    compare("fail", got.fail, want.fail);
    compare("unsupported", got.unsupported, want.unsupported);
    compare("timeout", got.timeout, want.timeout);
    compare("harness-error", got.harnessError, want.harnessError);
    for (const reason of ["noStrict", "raw", "async", "module"] as const) {
      compare(`not-run ${reason}`, got.notRun[reason], want.notRun[reason]);
    }
  }
  return lines;
}
