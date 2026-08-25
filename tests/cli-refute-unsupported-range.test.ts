import { describe, it, expect, vi, afterEach } from "vitest";
import * as fs from "node:fs";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { runTests, type RunResult } from "../engines/pabst/src/run.js";
import { RUN_ROOT } from "../src/run-dir.js";

// A domain that only fits after the safe-integer clamp is refused, not
// silently narrowed — the same NotTried + unsupported-range the prover
// emits. vitest is mocked at the module seam, as cli-unhealthy does.
vi.mock("../engines/pabst/src/run.js", () => ({ runTests: vi.fn() }));
const runTestsMock = vi.mocked(runTests);

const HUGE = "1000000000000000000000000000000";
const REASON = `endpoint ${HUGE} exceeds the safe integer range (±9007199254740991)`;

const allPassed = (n: number): RunResult => ({
  kind: "completed",
  json: {
    numPassedTests: n,
    numFailedTests: 0,
    success: true,
    testResults: [],
  },
});

describe("cli refute on unrepresentable domains", () => {
  useTempProject("lakatos-cli-refute-range-", {
    "mixed.ts": [
      `/** @ensures{big} forall (n: int ∈ [0, ${HUGE}]) { huge(n) >= 0 } */`,
      "export function huge(n: number): number { return n; }",
      "",
      "/** @ensures{pos} forall (n: int ∈ [0, 5)) { small(n) >= 0 } */",
      "export function small(n: number): number { return n; }",
      "",
    ].join("\n"),
    "allhuge.ts": `/** @ensures{big} forall (n: int ∈ [0, ${HUGE}]) { lone(n) >= 0 } */\nexport function lone(n: number): number { return n; }\n`,
    "emptied.ts": `/** @ensures{gone} forall (n: int ∈ [${HUGE}, ${HUGE}0]) { none(n) >= 0 } */\nexport function none(n: number): number { return n; }\n`,
  });

  afterEach(() => {
    runTestsMock.mockReset();
    fs.rmSync(RUN_ROOT, { recursive: true, force: true });
  });

  it("ships NotTried with kind and reason; the rest still run", () => {
    runTestsMock.mockReturnValue(allPassed(1));
    const { code, stdout, stderr } = runMain(["refute", "mixed.ts"]);
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      { file: "mixed.ts", function: "small", property: "pos", szs: "GaveUp" },
      {
        file: "mixed.ts",
        function: "huge",
        property: "big",
        szs: "NotTried",
        kind: "unsupported-range",
        reason: REASON,
      },
    ]);
    expect(stderr.join("\n")).toContain(
      "1 annotation not tried (unsupported range)",
    );
    // The warning the clamp used to print promised a domain nothing uses.
    expect(stderr.join("\n")).not.toContain("clamped to");
  });

  it("never runs vitest when every annotation is refused", () => {
    const { code, stdout } = runMain(["refute", "allhuge.ts"]);
    expect(code).toBe(0);
    expect(runTestsMock).not.toHaveBeenCalled();
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "allhuge.ts",
        function: "lone",
        property: "big",
        szs: "NotTried",
        kind: "unsupported-range",
        reason: REASON,
      },
    ]);
    expect(env.passed).toBe(0);
    expect(env.failed).toBe(0);
  });

  it("refuses a clamp-emptied interval instead of aborting the run", () => {
    const { code, stdout } = runMain(["refute", "emptied.ts"]);
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "emptied.ts",
        function: "none",
        property: "gone",
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          `endpoints ${HUGE} and ${HUGE}0 exceed ` +
          `the safe integer range (±9007199254740991)`,
      },
    ]);
  });

  it("keeps the metadata through an unhealthy run", () => {
    runTestsMock.mockReturnValue({
      kind: "broken-run",
      status: 1,
      messages: ["the suite failed to load"],
    });
    const { code, stdout } = runMain(["refute", "mixed.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      { file: "mixed.ts", function: "small", property: "pos", szs: "NotTried" },
      {
        file: "mixed.ts",
        function: "huge",
        property: "big",
        szs: "NotTried",
        kind: "unsupported-range",
        reason: REASON,
      },
    ]);
  });
});
