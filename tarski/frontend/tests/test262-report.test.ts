import { describe, it, expect } from "vitest";
import {
  diffExpectations,
  renderDetails,
  renderTable,
  tabulate,
  type DirectoryCounts,
  type Result,
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
  notRun: { noStrict: 0, raw: 0, async: 0, module: 0, ...notRun },
});

const ran = (
  directory: string,
  name: string,
  outcome: Result["outcome"],
): Result => ({
  path: `${directory}/${name}`,
  directory,
  plan: { kind: "run", source: "" },
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
      ran("test/a", "three.js", { class: "unsupported", kind: "ForStatement" }),
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
      ["noStrict", "raw", "async", "module"] as const
    ).map((reason) => ({
      path: `test/x/${reason}.js`,
      directory: "test/x",
      plan: { kind: "not-run", reason },
    }));
    expect(tabulate(results)).toEqual({
      "test/x": counts({}, { noStrict: 1, raw: 1, async: 1, module: 1 }),
    });
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
      ran("test/a", "five.js", { class: "unsupported", kind: "ForStatement" }),
      ran("test/a", "six.js", {
        class: "unsupported",
        kind: "SwitchStatement",
      }),
      ran("test/a", "seven.js", {
        class: "unsupported",
        kind: "SwitchStatement",
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
        "  SwitchStatement  2",
        "  ForStatement  1",
        "failures:",
        "  test/a/eight.js  Uncaught Test262Error: boom",
        "harness errors:",
        "  test/a/nine.js  no harness file nope.js",
        "timeouts:",
        "  test/a/ten.js",
      ].join("\n"),
    );
  });

  it("says nothing when everything passed", () => {
    expect(renderDetails([ran("test/a", "one.js", { class: "pass" })])).toBe(
      "",
    );
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
