// The table, the details under it, and the diff against the committed
// expectations.
//
// One row per directory, because that is the unit a slice is named by and
// the unit the expectations file pins. Skipped tests are in no row: what
// `intl402` and the parse-phase negatives amount to is a property of the
// pinned commit, not of the evaluator, so pinning their counts would make
// a test262 bump look like a regression here.

import type { NotRunReason, SkipReason } from "./plan.js";
import type { Outcome } from "./run.js";

/** The counts one directory's row carries. */
export interface DirectoryCounts {
  pass: number;
  fail: number;
  unsupported: number;
  timeout: number;
  harnessError: number;
  notRun: {
    noStrict: number;
    raw: number;
    async: number;
    module: number;
    budget: number;
  };
}

/**
 * What became of one test: a `Plan` with its assembled text dropped. A
 * result must not hold the source — the full run keeps a result per test
 * for the whole suite, and each source is the two preludes plus the test,
 * tens of kilobytes apiece. A `Plan` is assignable to this.
 */
export type Disposition =
  | { kind: "run"; negative?: { type: string } }
  | { kind: "not-run"; reason: NotRunReason }
  | { kind: "skip"; reason: SkipReason };

/** One test, planned and (unless skipped or not run) run. */
export interface Result {
  path: string;
  directory: string;
  plan: Disposition;
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
  notRun: { noStrict: 0, raw: 0, async: 0, module: 0, budget: 0 },
});

/** Every not-run reason, in the order the rows are written. */
const NOT_RUN_REASONS = [
  "noStrict",
  "raw",
  "async",
  "module",
  "budget",
] as const;

/** Every skip reason, in the order the rows are written. */
const SKIP_REASONS = [
  "parse-negative",
  "resolution-negative",
  "intl402",
] as const;

/** The not-run reasons summed: the single column the table shows. */
const notRunTotal = (counts: DirectoryCounts): number =>
  NOT_RUN_REASONS.reduce((sum, reason) => sum + counts.notRun[reason], 0);

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
  /* v8 ignore next 3 -- a Map's keys are distinct, so the comparator's
     equal arm is never taken. */
  return Object.fromEntries(
    [...rows.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)),
  );
}

/**
 * The first `depth` components of a directory: the unit the committed
 * results table is written in. A directory with fewer components than
 * that — `test/harness` — is its own key.
 */
export function groupKey(directory: string, depth = 3): string {
  return directory.split("/").slice(0, depth).join("/");
}

/**
 * A leaf table re-keyed to `depth` components and summed field by field,
 * sorted. `test/language/statements/for` and `test/language/statements/if`
 * become one `test/language/statements` row. This is the granularity the
 * committed results table is written in, and deliberately not the one
 * `expected.json` pins: the PR gate stays at the leaf.
 */
export function rollUp(
  counts: Record<string, DirectoryCounts>,
  depth = 3,
): Record<string, DirectoryCounts> {
  const rows = new Map<string, DirectoryCounts>();
  for (const [directory, row] of Object.entries(counts)) {
    const key = groupKey(directory, depth);
    let into = rows.get(key);
    if (into === undefined) {
      into = emptyCounts();
      rows.set(key, into);
    }
    add(into, row);
  }
  /* v8 ignore next 3 -- a Map's keys are distinct, so the comparator's
     equal arm is never taken. */
  return Object.fromEntries(
    [...rows.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)),
  );
}

/** `into += row`, field by field, including every not-run reason. */
function add(into: DirectoryCounts, row: DirectoryCounts): void {
  into.pass += row.pass;
  into.fail += row.fail;
  into.unsupported += row.unsupported;
  into.timeout += row.timeout;
  into.harnessError += row.harnessError;
  for (const reason of NOT_RUN_REASONS)
    into.notRun[reason] += row.notRun[reason];
}

/**
 * Everything the committed results files say. Nothing here differs
 * between two runs of the same binary over the same pin: no date, no
 * elapsed time, no run URL. Otherwise "commit the table when it changed"
 * would be "commit the table every week".
 */
export interface Summary {
  test262: { commit: string | null };
  slices: string[];
  timeoutMs: number;
  directories: Record<string, DirectoryCounts>;
  totals: DirectoryCounts;
  skipped: Record<SkipReason, number>;
  unsupported: Record<string, number>;
}

/** The results as the `Summary` the Markdown and the JSON are written from. */
export function summarise(
  results: readonly Result[],
  options: {
    commit: string | null;
    slices: readonly string[];
    timeoutMs: number;
  },
): Summary {
  const directories = rollUp(tabulate(results));
  const totals = emptyCounts();
  for (const row of Object.values(directories)) add(totals, row);
  // Every reason, zeros included, so the rows of the committed table are
  // stable as the evaluator grows into or out of them.
  const skipped = Object.fromEntries(
    SKIP_REASONS.map((reason) => [reason, 0]),
  ) as Record<SkipReason, number>;
  for (const result of results) {
    if (result.plan.kind === "skip") skipped[result.plan.reason] += 1;
  }
  return {
    test262: { commit: options.commit },
    slices: [...options.slices],
    timeoutMs: options.timeoutMs,
    directories,
    totals,
    skipped,
    unsupported: Object.fromEntries(histogram(results)),
  };
}

/**
 * The unsupported kinds, commonest first and ties broken by name.
 * Descending, because while the floor is what it is this histogram is the
 * actionable output: the head of it names the next slice to land.
 */
function histogram(results: readonly Result[]): [string, number][] {
  const kinds = new Map<string, number>();
  for (const result of results) {
    if (result.plan.kind !== "run") continue;
    if (result.outcome?.class === "unsupported")
      kinds.set(result.outcome.kind, (kinds.get(result.outcome.kind) ?? 0) + 1);
  }
  return [...kinds.entries()].sort(
    ([aKind, a], [bKind, b]) => b - a || (aKind < bKind ? -1 : 1),
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
  const widths: number[] = [];
  for (const row of [HEADERS, ...rows]) {
    for (const [column, cell] of row.entries()) {
      widths[column] = Math.max(widths[column] ?? 0, cell.length);
    }
  }
  const line = (cells: readonly string[]): string =>
    cells
      .map((cell, column) => {
        // The first column is the directory, and reads as a list; every
        // other is a count, and reads as a column of digits.
        /* v8 ignore next -- every row has one cell per header, so the
           width is always there; the fallback is `noUncheckedIndexedAccess`
           asking, not a case a caller can produce. */
        const width = widths[column] ?? cell.length;
        return column === 0 ? cell.padEnd(width) : cell.padStart(width);
      })
      .join("  ")
      .trimEnd();
  return [line(HEADERS), ...rows.map(line)].join("\n");
}

/**
 * `not run:`, `skipped:`, the unsupported histogram, and the three lists.
 * `lists: false` keeps the counts and drops the three lists: a whole-suite
 * run names tens of thousands of tests, and nobody reads that from a
 * scheduled job's log.
 */
export function renderDetails(
  results: readonly Result[],
  options: { lists: boolean } = { lists: true },
): string {
  const sections: string[] = [];

  const notRun = new Map<NotRunReason, number>();
  const skipped = new Map<SkipReason, number>();
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

  const kinds = histogram(results);
  if (kinds.length > 0) {
    sections.push(
      [
        "unsupported:",
        ...kinds.map(([kind, count]) => `  ${kind}  ${count}`),
      ].join("\n"),
    );
  }

  const list = (title: string, lines: readonly string[]): void => {
    if (options.lists && lines.length > 0)
      sections.push([title, ...lines].join("\n"));
  };
  list("failures:", failures);
  list("harness errors:", harnessErrors);
  list("timeouts:", timeouts);

  return sections.join("\n");
}

/** The columns of the committed table's first section. */
const MARKDOWN_HEADERS = [
  "directory",
  "tests",
  "pass",
  "fail",
  "unsupported",
  "timeout",
  "harness-error",
  "not-run",
];

/** Every count in a row summed: the denominator that row answers for. */
const rowTotal = (counts: DirectoryCounts): number =>
  counts.pass +
  counts.fail +
  counts.unsupported +
  counts.timeout +
  counts.harnessError +
  notRunTotal(counts);

/** One row of `MARKDOWN_HEADERS`, the directory first. */
const markdownRow = (directory: string, counts: DirectoryCounts): string[] => [
  directory,
  String(rowTotal(counts)),
  String(counts.pass),
  String(counts.fail),
  String(counts.unsupported),
  String(counts.timeout),
  String(counts.harnessError),
  String(notRunTotal(counts)),
];

/**
 * The document committed as `test262/results.md`. It is rendered the way
 * prettier would format it — width `max(3, widest cell)`, left cells
 * padded right and right-aligned cells padded left — so the committed
 * file passes the `Format` job as written rather than by exemption.
 */
export function renderMarkdown(summary: Summary): string {
  const commit =
    summary.test262.commit === null
      ? "an unknown commit"
      : `\`${summary.test262.commit}\``;
  const slices = summary.slices.map((slice) => `\`${slice}\``).join(", ");
  const seconds = summary.timeoutMs / 1000;
  const sections = [
    "# test262 results",
    `The evaluator run against test262 at ${commit}, over ${slices}, with a ${seconds}-second per-test timeout. Written by \`sh scripts/test262-full.sh\`; not edited by hand.`,
    "## By directory",
    markdownTable(
      MARKDOWN_HEADERS,
      ["left", ...MARKDOWN_HEADERS.slice(1).map(() => "right" as const)],
      [
        ...Object.entries(summary.directories).map(([directory, counts]) =>
          markdownRow(directory, counts),
        ),
        markdownRow("total", summary.totals),
      ],
    ),
    "## Not run and skipped",
    markdownTable(
      ["kind", "tests", "where"],
      ["left", "right", "left"],
      [
        ...NOT_RUN_REASONS.map((reason) => [
          reason,
          String(summary.totals.notRun[reason]),
          "not-run column",
        ]),
        ...SKIP_REASONS.map((reason) => [
          reason,
          String(summary.skipped[reason]),
          "outside the table",
        ]),
      ],
    ),
  ];
  const kinds = Object.entries(summary.unsupported);
  if (kinds.length > 0) {
    sections.push(
      "## Unsupported",
      markdownTable(
        ["kind", "tests"],
        ["left", "right"],
        kinds.map(([kind, count]) => [kind, String(count)]),
      ),
    );
  }
  return `${sections.join("\n\n")}\n`;
}

/** Prettier's default print width, which both renderers here obey. */
const PRINT_WIDTH = 80;

/**
 * The document committed as `test262/results.json`. `JSON.stringify`'s
 * indentation is prettier's too, with one difference: prettier puts an
 * array that fits the print width on one line, and `slices` is the only
 * array in a `Summary`. Written that way, the committed file passes the
 * `Format` job as written, like `results.md` beside it.
 */
export function renderJson(summary: Summary): string {
  const body = JSON.stringify(summary, null, 2);
  // Prettier's spacing, not `JSON.stringify`'s: a comma and a space.
  const slices = summary.slices
    .map((slice) => JSON.stringify(slice))
    .join(", ");
  const inline = `  "slices": [${slices}],`;
  if (inline.length > PRINT_WIDTH) return `${body}\n`;
  return `${body.replace(/ {2}"slices": \[[\s\S]*?\n {2}\],/, () => inline)}\n`;
}

/** Which way a column's cells are padded, and how its rule is spelled. */
type Align = "left" | "right";

/** A GitHub-flavoured table, padded the way prettier pads one. */
function markdownTable(
  header: readonly string[],
  align: readonly Align[],
  rows: readonly (readonly string[])[],
): string {
  // Three is prettier's floor: a rule needs `---` or `--:` to be one.
  const widths = header.map((cell) => Math.max(3, cell.length));
  for (const row of rows) {
    for (const [column, cell] of row.entries()) {
      /* v8 ignore next -- every row has one cell per header, so the width
         is always there; the fallback is `noUncheckedIndexedAccess`
         asking, not a case a caller can produce. */
      widths[column] = Math.max(widths[column] ?? 3, cell.length);
    }
  }
  const cells = (row: readonly string[]): string =>
    `| ${row
      .map((cell, column) => {
        /* v8 ignore next 2 -- as above: one cell per header, one
           alignment per header. */
        const width = widths[column] ?? cell.length;
        return align[column] === "right"
          ? cell.padStart(width)
          : cell.padEnd(width);
      })
      .join(" | ")} |`;
  const rule = `| ${widths
    .map((width, column) =>
      align[column] === "right"
        ? `${"-".repeat(width - 1)}:`
        : "-".repeat(width),
    )
    .join(" | ")} |`;
  return [cells(header), rule, ...rows.map(cells)].join("\n");
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
    for (const reason of NOT_RUN_REASONS) {
      compare(`not-run ${reason}`, got.notRun[reason], want.notRun[reason]);
    }
  }
  return lines;
}
