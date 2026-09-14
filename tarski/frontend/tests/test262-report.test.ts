import { describe, it, expect } from "vitest";
import { format } from "prettier";
import {
  diffExpectations,
  renderDetails,
  renderJson,
  renderMarkdown,
  renderTable,
  rollUp,
  summarise,
  tabulate,
  type DirectoryCounts,
  type Result,
  type Summary,
} from "../src/test262/report.js";

const counts = (
  partial: Partial<Omit<DirectoryCounts, "notRun">> = {},
  notRun: Partial<DirectoryCounts["notRun"]> = {},
): DirectoryCounts => ({
  pass: 0,
  fail: 0,
  unsupported: 0,
  timeout: 0,
  harnessError: 0,
  ...partial,
  notRun: { noStrict: 0, raw: 0, async: 0, module: 0, budget: 0, ...notRun },
});

const ran = (
  directory: string,
  name: string,
  outcome: Result["outcome"],
): Result => ({
  path: `${directory}/${name}`,
  directory,
  plan: { kind: "run" },
  outcome,
});

describe("tabulate", () => {
  it("groups by directory, sorted, and omits skipped tests", () => {
    const results: Result[] = [
      ran("test/b", "one.js", { class: "pass" }),
      ran("test/a", "two.js", {
        class: "fail",
        detail: "Uncaught Test262Error: boom",
      }),
      ran("test/a", "three.js", {
        class: "unsupported",
        kind: "ForOfStatement",
      }),
      ran("test/a", "four.js", { class: "timeout" }),
      ran("test/a", "five.js", {
        class: "harness-error",
        detail: "no such file",
      }),
      {
        path: "test/a/six.js",
        directory: "test/a",
        plan: { kind: "not-run", reason: "async" },
      },
      {
        path: "test/intl402/seven.js",
        directory: "test/intl402",
        plan: { kind: "skip", reason: "intl402" },
      },
    ];
    expect(tabulate(results)).toEqual({
      "test/a": counts(
        { fail: 1, unsupported: 1, timeout: 1, harnessError: 1 },
        { async: 1 },
      ),
      "test/b": counts({ pass: 1 }),
    });
    expect(Object.keys(tabulate(results))).toEqual(["test/a", "test/b"]);
  });

  it("counts each not-run reason in its own column", () => {
    const results: Result[] = (
      ["noStrict", "raw", "async", "module", "budget"] as const
    ).map((reason) => ({
      path: `test/x/${reason}.js`,
      directory: "test/x",
      plan: { kind: "not-run", reason },
    }));
    expect(tabulate(results)).toEqual({
      "test/x": counts(
        {},
        { noStrict: 1, raw: 1, async: 1, module: 1, budget: 1 },
      ),
    });
  });
});

describe("rollUp", () => {
  it("folds leaf directories into three components and sums every field", () => {
    expect(
      rollUp({
        "test/language/statements/for": counts(
          { pass: 1, fail: 2, unsupported: 3, timeout: 4, harnessError: 5 },
          { noStrict: 6, raw: 7 },
        ),
        "test/language/statements/if": counts(
          {
            pass: 10,
            fail: 20,
            unsupported: 30,
            timeout: 40,
            harnessError: 50,
          },
          { async: 8, module: 9, budget: 10 },
        ),
      }),
    ).toEqual({
      "test/language/statements": counts(
        { pass: 11, fail: 22, unsupported: 33, timeout: 44, harnessError: 55 },
        { noStrict: 6, raw: 7, async: 8, module: 9, budget: 10 },
      ),
    });
  });

  it("takes the depth as an argument", () => {
    expect(
      Object.keys(
        rollUp(
          {
            "test/language/statements/for": counts({ pass: 1 }),
            "test/built-ins/Math/abs": counts({ pass: 1 }),
          },
          2,
        ),
      ),
    ).toEqual(["test/built-ins", "test/language"]);
  });

  it("leaves a directory shallower than the depth alone, and sorts", () => {
    expect(
      Object.keys(
        rollUp({
          "test/language/expressions/addition": counts(),
          "test/harness": counts(),
          "test/built-ins/Math/abs": counts(),
        }),
      ),
    ).toEqual([
      "test/built-ins/Math",
      "test/harness",
      "test/language/expressions",
    ]);
  });
});

describe("renderTable", () => {
  it("matches the shape the issue spells", () => {
    expect(
      renderTable({
        "test/harness": counts({ unsupported: 99 }, { async: 17 }),
        "test/language/expressions": counts({ pass: 101, fail: 9 }),
      }),
    ).toBe(
      [
        "directory                  pass  fail  unsupported  timeout  harness-error  not-run",
        "test/harness                  0     0           99        0              0       17",
        "test/language/expressions   101     9            0        0              0        0",
      ].join("\n"),
    );
  });

  it("renders the headers alone for an empty run", () => {
    expect(renderTable({})).toBe(
      "directory  pass  fail  unsupported  timeout  harness-error  not-run",
    );
  });
});

describe("renderDetails", () => {
  it("lists the reasons, the kind histogram, and the three lists", () => {
    const results: Result[] = [
      {
        path: "test/a/one.js",
        directory: "test/a",
        plan: { kind: "not-run", reason: "async" },
      },
      {
        path: "test/a/two.js",
        directory: "test/a",
        plan: { kind: "not-run", reason: "async" },
      },
      {
        path: "test/a/three.js",
        directory: "test/a",
        plan: { kind: "not-run", reason: "raw" },
      },
      {
        path: "test/a/four.js",
        directory: "test/a",
        plan: { kind: "skip", reason: "parse-negative" },
      },
      ran("test/a", "five.js", {
        class: "unsupported",
        kind: "ForOfStatement",
      }),
      ran("test/a", "six.js", {
        class: "unsupported",
        kind: "TemplateExpression",
      }),
      ran("test/a", "seven.js", {
        class: "unsupported",
        kind: "TemplateExpression",
      }),
      ran("test/a", "eight.js", {
        class: "fail",
        detail: "Uncaught Test262Error: boom",
      }),
      ran("test/a", "nine.js", {
        class: "harness-error",
        detail: "no harness file nope.js",
      }),
      ran("test/a", "ten.js", { class: "timeout" }),
      ran("test/a", "eleven.js", { class: "pass" }),
    ];
    expect(renderDetails(results)).toBe(
      [
        "not run:",
        "  async  2",
        "  raw  1",
        "skipped:",
        "  parse-negative  1",
        "unsupported:",
        "  TemplateExpression  2",
        "  ForOfStatement  1",
        "failures:",
        "  test/a/eight.js  Uncaught Test262Error: boom",
        "harness errors:",
        "  test/a/nine.js  no harness file nope.js",
        "timeouts:",
        "  test/a/ten.js",
      ].join("\n"),
    );
  });

  it("breaks a tie in the histogram by name, whichever came first", () => {
    const golden = "unsupported:\n  ForOfStatement  1\n  TemplateExpression  1";
    expect(
      renderDetails([
        ran("test/a", "one.js", {
          class: "unsupported",
          kind: "TemplateExpression",
        }),
        ran("test/a", "two.js", {
          class: "unsupported",
          kind: "ForOfStatement",
        }),
      ]),
    ).toBe(golden);
    expect(
      renderDetails([
        ran("test/a", "one.js", {
          class: "unsupported",
          kind: "ForOfStatement",
        }),
        ran("test/a", "two.js", {
          class: "unsupported",
          kind: "TemplateExpression",
        }),
      ]),
    ).toBe(golden);
  });

  it("says nothing when everything passed", () => {
    expect(renderDetails([ran("test/a", "one.js", { class: "pass" })])).toBe(
      "",
    );
  });

  it("keeps the counts and drops the three lists under lists: false", () => {
    const results: Result[] = [
      {
        path: "test/a/one.js",
        directory: "test/a",
        plan: { kind: "not-run", reason: "budget" },
      },
      {
        path: "test/a/two.js",
        directory: "test/a",
        plan: { kind: "skip", reason: "intl402" },
      },
      ran("test/a", "three.js", {
        class: "unsupported",
        kind: "SwitchStatement",
      }),
      ran("test/a", "four.js", {
        class: "fail",
        detail: "Uncaught Test262Error: boom",
      }),
      ran("test/a", "five.js", {
        class: "harness-error",
        detail: "no harness file nope.js",
      }),
      ran("test/a", "six.js", { class: "timeout" }),
    ];
    expect(renderDetails(results, { lists: false })).toBe(
      [
        "not run:",
        "  budget  1",
        "skipped:",
        "  intl402  1",
        "unsupported:",
        "  SwitchStatement  1",
      ].join("\n"),
    );
  });
});

const skipped = (
  directory: string,
  reason: "intl402" | "parse-negative",
): Result => ({
  path: `${directory}/skip.js`,
  directory,
  plan: { kind: "skip", reason },
});

/** One run of every class, across two depth-three groups. */
const sample: Result[] = [
  ran("test/built-ins/Math/abs", "one.js", { class: "pass" }),
  ran("test/built-ins/Math/abs", "two.js", {
    class: "unsupported",
    kind: "SwitchStatement",
  }),
  ran("test/built-ins/Math/cos", "three.js", {
    class: "fail",
    detail: "Uncaught Test262Error: boom",
  }),
  ran("test/built-ins/Math/cos", "four.js", {
    class: "unsupported",
    kind: "SwitchStatement",
  }),
  ran("test/language/statements/for", "five.js", { class: "timeout" }),
  ran("test/language/statements/for", "six.js", {
    class: "harness-error",
    detail: "no harness file nope.js",
  }),
  ran("test/language/statements/if", "seven.js", {
    class: "unsupported",
    kind: "ForStatement",
  }),
  {
    path: "test/language/statements/if/eight.js",
    directory: "test/language/statements/if",
    plan: { kind: "not-run", reason: "budget" },
  },
  {
    path: "test/language/statements/if/nine.js",
    directory: "test/language/statements/if",
    plan: { kind: "not-run", reason: "async" },
  },
  skipped("test/intl402/Collator", "intl402"),
  skipped("test/language/statements/if", "parse-negative"),
];

const summaryOf = (
  results: readonly Result[],
  commit: string | null,
): Summary =>
  summarise(results, {
    commit,
    slices: ["test/language", "test/built-ins", "test/intl402"],
    timeoutMs: 10_000,
  });

const COMMIT = "419d3e0a2273ba01a3bfcbec423f2801425b8e93";

describe("summarise", () => {
  it("rolls the rows up, totals them, and copies what it was told", () => {
    const summary = summaryOf(sample, COMMIT);
    expect(summary.test262).toEqual({ commit: COMMIT });
    expect(summary.slices).toEqual([
      "test/language",
      "test/built-ins",
      "test/intl402",
    ]);
    expect(summary.timeoutMs).toBe(10_000);
    expect(summary.directories).toEqual({
      "test/built-ins/Math": counts({ pass: 1, fail: 1, unsupported: 2 }),
      "test/language/statements": counts(
        { unsupported: 1, timeout: 1, harnessError: 1 },
        { async: 1, budget: 1 },
      ),
    });
    expect(summary.totals).toEqual(
      counts(
        { pass: 1, fail: 1, unsupported: 3, timeout: 1, harnessError: 1 },
        { async: 1, budget: 1 },
      ),
    );
  });

  it("carries every skip reason, zeros included, and the histogram in order", () => {
    const summary = summaryOf(sample, COMMIT);
    expect(summary.skipped).toEqual({
      "parse-negative": 1,
      "resolution-negative": 0,
      intl402: 1,
    });
    expect(Object.entries(summary.unsupported)).toEqual([
      ["SwitchStatement", 2],
      ["ForStatement", 1],
    ]);
  });

  it("passes a null commit through", () => {
    expect(summaryOf(sample, null).test262).toEqual({ commit: null });
  });
});

describe("renderMarkdown", () => {
  it("matches the committed document's shape", () => {
    expect(renderMarkdown(summaryOf(sample, COMMIT))).toBe(
      [
        "# test262 results",
        "",
        "The evaluator run against test262 at `419d3e0a2273ba01a3bfcbec423f2801425b8e93`, over `test/language`, `test/built-ins`, `test/intl402`, with a 10-second per-test timeout. Written by `sh scripts/test262-full.sh`; not edited by hand.",
        "",
        "## By directory",
        "",
        "| directory                | tests | pass | fail | unsupported | timeout | harness-error | not-run |",
        "| ------------------------ | ----: | ---: | ---: | ----------: | ------: | ------------: | ------: |",
        "| test/built-ins/Math      |     4 |    1 |    1 |           2 |       0 |             0 |       0 |",
        "| test/language/statements |     5 |    0 |    0 |           1 |       1 |             1 |       2 |",
        "| total                    |     9 |    1 |    1 |           3 |       1 |             1 |       2 |",
        "",
        "## Not run and skipped",
        "",
        "| kind                | tests | where             |",
        "| ------------------- | ----: | ----------------- |",
        "| noStrict            |     0 | not-run column    |",
        "| raw                 |     0 | not-run column    |",
        "| async               |     1 | not-run column    |",
        "| module              |     0 | not-run column    |",
        "| budget              |     1 | not-run column    |",
        "| parse-negative      |     1 | outside the table |",
        "| resolution-negative |     0 | outside the table |",
        "| intl402             |     1 | outside the table |",
        "",
        "## Unsupported",
        "",
        "| kind            | tests |",
        "| --------------- | ----: |",
        "| SwitchStatement |     2 |",
        "| ForStatement    |     1 |",
        "",
      ].join("\n"),
    );
  });

  it("names an unknown commit when there is none", () => {
    expect(renderMarkdown(summaryOf(sample, null))).toContain(
      "at an unknown commit, over",
    );
  });

  it("omits the Unsupported table when nothing was refused", () => {
    const markdown = renderMarkdown(
      summaryOf([ran("test/a/b", "one.js", { class: "pass" })], COMMIT),
    );
    expect(markdown).not.toContain("## Unsupported");
    expect(markdown).toContain("## Not run and skipped");
  });

  // The committed file is checked by the `Format` job like every other
  // Markdown file in the tree, so the renderer has to pad the way prettier
  // pads. Prettier's own formatter is the only honest witness to that.
  it("is prettier-clean as written", async () => {
    const markdown = renderMarkdown(summaryOf(sample, COMMIT));
    expect(await format(markdown, { parser: "markdown" })).toBe(markdown);
  });

  it("is prettier-clean when a directory outgrows every header", async () => {
    const long = "test/language/an-extremely-long-directory-name-indeed";
    const markdown = renderMarkdown(
      summaryOf([ran(long, "one.js", { class: "pass" })], COMMIT),
    );
    expect(markdown).toContain(`| ${long} |`);
    expect(await format(markdown, { parser: "markdown" })).toBe(markdown);
  });
});

describe("renderJson", () => {
  it("is prettier-clean as written", async () => {
    const json = renderJson(summaryOf(sample, COMMIT));
    expect(json).toContain(
      '"slices": ["test/language", "test/built-ins", "test/intl402"]',
    );
    expect(await format(json, { parser: "json" })).toBe(json);
  });

  it("is prettier-clean when the slices outgrow the print width", async () => {
    const json = renderJson(
      summarise([ran("test/a/b", "one.js", { class: "pass" })], {
        commit: COMMIT,
        slices: [
          "test/language/expressions/assignment",
          "test/language/statements/class",
          "test/built-ins/TypedArray/prototype",
        ],
        timeoutMs: 10_000,
      }),
    );
    expect(json).toContain('"slices": [\n');
    expect(await format(json, { parser: "json" })).toBe(json);
  });

  it("parses back to the summary it was given", () => {
    const summary = summaryOf(sample, COMMIT);
    expect(JSON.parse(renderJson(summary))).toEqual(summary);
  });
});

describe("diffExpectations", () => {
  const actual = { "test/harness": counts({ unsupported: 99 }, { async: 17 }) };

  it("is empty when the counts agree", () => {
    expect(
      diffExpectations(actual, {
        "test/harness": counts({ unsupported: 99 }, { async: 17 }),
      }),
    ).toEqual([]);
  });

  it("names a count that differs", () => {
    expect(
      diffExpectations(actual, {
        "test/harness": counts({ unsupported: 98, pass: 1 }, { async: 17 }),
      }),
    ).toEqual([
      "test/harness: pass expected 1, got 0",
      "test/harness: unsupported expected 98, got 99",
    ]);
  });

  it("names a not-run reason that differs", () => {
    expect(
      diffExpectations(actual, {
        "test/harness": counts({ unsupported: 99 }, { async: 16 }),
      }),
    ).toEqual(["test/harness: not-run async expected 16, got 17"]);
  });

  it("reports a budget exhaustion, so a truncated run is never silent", () => {
    expect(
      diffExpectations(
        {
          "test/harness": counts({ unsupported: 99 }, { async: 17, budget: 3 }),
        },
        { "test/harness": counts({ unsupported: 99 }, { async: 17 }) },
      ),
    ).toEqual(["test/harness: not-run budget expected 0, got 3"]);
  });

  it("names a directory that is not in the expectations", () => {
    expect(diffExpectations(actual, {})).toEqual([
      "test/harness: not in the expectations",
    ]);
  });

  it("names a directory that was expected but not run", () => {
    expect(diffExpectations({}, { "test/harness": counts() })).toEqual([
      "test/harness: expected but not run",
    ]);
  });
});
