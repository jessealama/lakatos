import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { HarnessError, listTests, planTest } from "../src/test262/plan.js";

// The fake tree: one file per decision the planner makes, checked in so
// that the unit tests and the end-to-end run read the same bytes.
const ROOT = fileURLToPath(new URL("fixtures/test262", import.meta.url));

const read = (relative: string): string =>
  readFileSync(path.join(ROOT, relative), "utf8");

const readHarness = (name: string): string => {
  try {
    return readFileSync(path.join(ROOT, "harness", name), "utf8");
  } catch {
    throw new HarnessError(`no harness file ${name}`);
  }
};

const plan = (relative: string) =>
  planTest(relative, read(relative), readHarness);

describe("planTest", () => {
  describe("skips", () => {
    it("skips intl402 by path", () => {
      expect(plan("test/intl402/x.js")).toEqual({
        kind: "skip",
        reason: "intl402",
      });
    });

    it("skips a parse-phase negative", () => {
      expect(plan("test/skipped/parse-negative.js")).toEqual({
        kind: "skip",
        reason: "parse-negative",
      });
    });

    it("skips a resolution-phase negative", () => {
      expect(plan("test/skipped/resolution-negative.js")).toEqual({
        kind: "skip",
        reason: "resolution-negative",
      });
    });

    // The resolution-phase negative is also flagged `module`, and the
    // phase is read first: a skip says more than a not-run row.
    it("prefers the phase to the module flag", () => {
      expect(plan("test/skipped/resolution-negative.js").kind).toBe("skip");
    });
  });

  describe("not run", () => {
    it("files a module test", () => {
      expect(plan("test/not-run/module.js")).toEqual({
        kind: "not-run",
        reason: "module",
      });
    });

    it("files a raw test that is not already strict", () => {
      expect(plan("test/not-run/raw-sloppy.js")).toEqual({
        kind: "not-run",
        reason: "raw",
      });
    });

    it("files a noStrict test", () => {
      expect(plan("test/not-run/no-strict.js")).toEqual({
        kind: "not-run",
        reason: "noStrict",
      });
    });

    it("files an async test", () => {
      expect(plan("test/not-run/async.js")).toEqual({
        kind: "not-run",
        reason: "async",
      });
    });
  });

  describe("runs", () => {
    it("prepends the strict directive, then sta.js, then assert.js, then the test", () => {
      const result = plan("test/pass/passes.js");
      if (result.kind !== "run")
        throw new Error(`expected a run, got ${result.kind}`);
      expect(result.source.startsWith('"use strict";\n')).toBe(true);
      const sta = result.source.indexOf("function Test262Error(message)");
      const assert = result.source.indexOf(
        "function assert(mustBeTrue, message)",
      );
      const test = result.source.indexOf("assert.sameValue(1 + 1, 2");
      expect(sta).toBeGreaterThan(0);
      expect(assert).toBeGreaterThan(sta);
      expect(test).toBeGreaterThan(assert);
      expect(result.negative).toBeUndefined();
    });

    it("evaluates the includes after the preludes, in the order given", () => {
      const result = plan("test/unsupported/include-unsupported.js");
      if (result.kind !== "run")
        throw new Error(`expected a run, got ${result.kind}`);
      expect(result.source.indexOf("function kindOf(x)")).toBeGreaterThan(
        result.source.indexOf("function assert(mustBeTrue, message)"),
      );
      expect(
        result.source.indexOf("assert.sameValue(kindOf(1)"),
      ).toBeGreaterThan(result.source.indexOf("function kindOf(x)"));
    });

    it("throws HarnessError for an include that is not there", () => {
      expect(() => plan("test/harness-error/missing-include.js")).toThrow(
        HarnessError,
      );
    });

    it("runs onlyStrict as the plain run", () => {
      const result = plan("test/pass/only-strict.js");
      if (result.kind !== "run")
        throw new Error(`expected a run, got ${result.kind}`);
      expect(result.source.startsWith('"use strict";\n')).toBe(true);
      expect(result.source).toContain("function assert(mustBeTrue, message)");
    });

    it("runs a strict raw test alone and unmodified", () => {
      const result = plan("test/pass/raw-strict.js");
      expect(result).toEqual({
        kind: "run",
        source: read("test/pass/raw-strict.js"),
      });
    });

    it("carries a runtime negative's class", () => {
      const result = plan("test/pass/negative-runtime.js");
      if (result.kind !== "run")
        throw new Error(`expected a run, got ${result.kind}`);
      expect(result.negative).toEqual({ type: "TypeError" });
    });
  });
});

describe("listTests", () => {
  it("lists every test under a directory, sorted", () => {
    expect(listTests(ROOT, ["test/pass"])).toEqual([
      "test/pass/includes-block-list.js",
      "test/pass/negative-runtime.js",
      "test/pass/negative-test262error.js",
      "test/pass/only-strict.js",
      "test/pass/passes.js",
      "test/pass/raw-strict.js",
    ]);
  });

  it("excludes module fixtures", () => {
    expect(listTests(ROOT, ["test/skipped"])).toEqual([
      "test/skipped/parse-negative.js",
      "test/skipped/resolution-negative.js",
    ]);
  });

  it("accepts a single file as a slice", () => {
    expect(listTests(ROOT, ["test/pass/passes.js"])).toEqual([
      "test/pass/passes.js",
    ]);
  });

  it("ignores a single file that is a module fixture", () => {
    expect(listTests(ROOT, ["test/skipped/x_FIXTURE.js"])).toEqual([]);
  });

  it("recurses, and sorts across slices", () => {
    expect(listTests(ROOT, ["test/timeout", "test/intl402"])).toEqual([
      "test/intl402/x.js",
      "test/timeout/loops.js",
    ]);
  });
});
