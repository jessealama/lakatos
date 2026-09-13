import { describe, it, expect, afterAll } from "vitest";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { classify, runOne, type SpawnOutcome } from "../src/test262/run.js";
import { planTest } from "../src/test262/plan.js";

const ROOT = fileURLToPath(new URL("fixtures/test262", import.meta.url));
const FAKE = fileURLToPath(
  new URL("fixtures/fake-tarski.mjs", import.meta.url),
);

const spawned = (partial: Partial<SpawnOutcome>): SpawnOutcome => ({
  status: 0,
  signal: null,
  stderr: "",
  ...partial,
});

describe("classify", () => {
  it("reads a killed process as the timeout the runner imposed", () => {
    expect(
      classify(spawned({ status: null, signal: "SIGTERM" }), undefined),
    ).toEqual({
      class: "timeout",
    });
  });

  it("reads ETIMEDOUT as a timeout", () => {
    const error = Object.assign(new Error("timed out"), { code: "ETIMEDOUT" });
    expect(classify(spawned({ status: null, error }), undefined)).toEqual({
      class: "timeout",
    });
  });

  it("reads any other spawn error as the runner's own machinery", () => {
    const error = Object.assign(new Error("spawn ENOENT"), { code: "ENOENT" });
    expect(classify(spawned({ status: null, error }), undefined)).toEqual({
      class: "harness-error",
      detail: "spawn ENOENT",
    });
  });

  it("reads exit 3 as unsupported, with the kind", () => {
    expect(
      classify(
        spawned({ status: 3, stderr: "unsupported: ForStatement\n" }),
        undefined,
      ),
    ).toEqual({ class: "unsupported", kind: "ForStatement" });
  });

  it("keeps the whole line when exit 3 names no kind", () => {
    expect(
      classify(spawned({ status: 3, stderr: "something else\n" }), undefined),
    ).toEqual({
      class: "unsupported",
      kind: "something else",
    });
  });

  it("reads exit 0 as a pass", () => {
    expect(classify(spawned({ status: 0 }), undefined)).toEqual({
      class: "pass",
    });
  });

  it("fails a negative test that completed", () => {
    expect(classify(spawned({ status: 0 }), { type: "TypeError" })).toEqual({
      class: "fail",
      detail: "expected an uncaught TypeError, the script completed",
    });
  });

  it("passes a negative test whose class matches", () => {
    expect(
      classify(spawned({ status: 1, stderr: "Uncaught TypeError: t\n" }), {
        type: "TypeError",
      }),
    ).toEqual({ class: "pass" });
  });

  // `Test262Error` is not an `Error` subclass, so this is the case the
  // binary's own-ToString report exists for.
  it("passes a negative Test262Error", () => {
    expect(
      classify(spawned({ status: 1, stderr: "Uncaught Test262Error: m\n" }), {
        type: "Test262Error",
      }),
    ).toEqual({ class: "pass" });
  });

  it("fails a negative test that threw the wrong class", () => {
    expect(
      classify(spawned({ status: 1, stderr: "Uncaught RangeError: r\n" }), {
        type: "TypeError",
      }),
    ).toEqual({
      class: "fail",
      detail: "expected an uncaught TypeError, got Uncaught RangeError: r",
    });
  });

  it("fails a negative test that threw something with no class name", () => {
    expect(
      classify(spawned({ status: 1, stderr: "Uncaught 1\n" }), {
        type: "TypeError",
      }),
    ).toEqual({
      class: "fail",
      detail: "expected an uncaught TypeError, got Uncaught 1",
    });
  });

  it("reads an abrupt-completion report as carrying no class", () => {
    expect(
      classify(
        spawned({
          status: 1,
          stderr:
            "Uncaught: abrupt completion outside any loop, label, or function\n",
        }),
        { type: "SyntaxError" },
      ),
    ).toEqual({
      class: "fail",
      detail:
        "expected an uncaught SyntaxError, got Uncaught: abrupt completion outside any loop, label, or function",
    });
  });

  it("fails an ordinary test that threw", () => {
    expect(
      classify(
        spawned({ status: 1, stderr: "Uncaught Test262Error: boom\n" }),
        undefined,
      ),
    ).toEqual({ class: "fail", detail: "Uncaught Test262Error: boom" });
  });

  it("reads exit 2 as the runner's own machinery", () => {
    expect(
      classify(
        spawned({ status: 2, stderr: "tarski: t.json: malformed\n" }),
        undefined,
      ),
    ).toEqual({ class: "harness-error", detail: "tarski: t.json: malformed" });
  });

  it("reads any other status as the runner's own machinery", () => {
    expect(classify(spawned({ status: 7 }), undefined)).toEqual({
      class: "harness-error",
      detail: "exit 7",
    });
  });
});

describe("runOne", () => {
  const scratch = mkdtempSync(path.join(tmpdir(), "test262-run-"));
  afterAll(() => rmSync(scratch, { recursive: true, force: true }));

  const readHarness = (name: string): string =>
    readFileSync(path.join(ROOT, "harness", name), "utf8");
  const plan = (relative: string) => {
    const result = planTest(
      relative,
      readFileSync(path.join(ROOT, relative), "utf8"),
      readHarness,
    );
    if (result.kind !== "run")
      throw new Error(`expected a run, got ${result.kind}`);
    return result;
  };

  it("runs a passing test through the binary", () => {
    expect(runOne(plan("test/pass/passes.js"), FAKE, 10_000, scratch)).toEqual({
      class: "pass",
    });
  });

  it("runs a failing test through the binary", () => {
    expect(
      runOne(plan("test/fail/assert-fails.js"), FAKE, 10_000, scratch),
    ).toEqual({
      class: "fail",
      detail: "Uncaught Test262Error: boom",
    });
  });

  // The parse-phase negatives are skipped, so a source that does not
  // parse is the runner's own machinery failing rather than a test
  // getting what it asked for.
  it("files a source that does not parse as a harness error", () => {
    const outcome = runOne(
      plan("test/harness-error/syntax-error.js"),
      FAKE,
      10_000,
      scratch,
    );
    expect(outcome.class).toBe("harness-error");
  });

  it("imposes the timeout it was given", () => {
    expect(runOne(plan("test/timeout/loops.js"), FAKE, 200, scratch)).toEqual({
      class: "timeout",
    });
  });
});
