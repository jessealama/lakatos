import { describe, it, expect } from "vitest";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";

describe("check stub", () => {
  useTempProject("lakatos-cli-stub-", {
    "annotated.ts": `/** @ensures{pos} forall (n: nat) { annotated(n) >= 0 } */\nexport function annotated(n: number): number { return n; }\n`,
    "malformed.ts": `/** @ensures{shapely} for every (n: nat), malformed(n) >= 0 */\nexport function malformed(n: number): number { return n; }\n`,
    "clampempty.ts": `/** @ensures{narrow} forall (x: int ∈ [1000000000000000000000000000000, 10000000000000000000000000000000]) { clampempty(x) >= 0 } */\nexport function clampempty(x: number): number { return x; }\n`,
    "inverted.ts": `/** @ensures{backwards} forall (x: int ∈ [5, 3]) { inverted(x) >= 0 } */\nexport function inverted(x: number): number { return x; }\n`,
    "clampmixed.ts": `/** @ensures{fine} forall (x: int ∈ [0, 5)) { fine(x) >= 0 } */\nexport function fine(x: number): number { return x; }\n\n/** @ensures{narrow} forall (x: int ∈ [1000000000000000000000000000000, 10000000000000000000000000000000]) { gone(x) >= 0 } */\nexport function gone(x: number): number { return x; }\n`,
    "clampwide.ts": `/** @ensures{big} forall (x: int ∈ [0, 1000000000000000000000000000000]) { wide(x) >= 0 } */\nexport function wide(x: number): number { return x; }\n`,
  });

  it("lists every annotation as NotTried and exits 1", async () => {
    const { code, stdout, stderr } = await runMain(["check", "annotated.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toEqual({
      file: "annotated.ts",
      function: "annotated",
      property: "pos",
      szs: "NotTried",
    });
    expect(env.seed).toBeUndefined();
    expect(env.generated).toBeUndefined();
    expect(env.passed).toBeUndefined();
    expect(env.failed).toBeUndefined();
    expect(stderr.join("\n")).toContain("check is not implemented yet");
  });

  it("still exits 2 on a formula lemma itself cannot parse", async () => {
    const { code, stderr } = await runMain(["check", "malformed.ts"]);
    expect(code).toBe(2);
    const diagnostics = stderr;
    expect(diagnostics).toHaveLength(1);
    expect(diagnostics[0]).toContain("malformed.ts:1: @ensures{shapely}:");
    expect(diagnostics[0]).toContain("expected 'forall'");
  });

  // A clamp-emptied interval parses, so it passes the shared gate; the
  // stub contains it per annotation exactly as both engines do.
  it("reports an interval the safe-integer clamp empties as unsupported-range", async () => {
    const { code, stdout, stderr } = await runMain(["check", "clampempty.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "clampempty.ts",
        function: "clampempty",
        property: "narrow",
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          "endpoints 1000000000000000000000000000000 and 10000000000000000000000000000000 " +
          "exceed the safe integer range (±9007199254740991)",
      },
    ]);
    expect(stderr.join("\n")).toContain(
      "1 annotation not tried (unsupported range)",
    );
    expect(stderr.join("\n")).not.toContain("empty interval");
  });

  it("keeps the refused annotation beside the rest, in source order", async () => {
    const { code, stdout } = await runMain(["check", "clampmixed.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "clampmixed.ts",
        function: "fine",
        property: "fine",
        szs: "NotTried",
      },
      {
        file: "clampmixed.ts",
        function: "gone",
        property: "narrow",
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          "endpoints 1000000000000000000000000000000 and 10000000000000000000000000000000 " +
          "exceed the safe integer range (±9007199254740991)",
      },
    ]);
  });

  // Nonempty after the clamp, but the clamped domain denotes a narrower
  // statement than the one written; both engines refuse it, so check does.
  it("reports a merely clamped interval as unsupported-range too", async () => {
    const { code, stdout } = await runMain(["check", "clampwide.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "clampwide.ts",
        function: "wide",
        property: "big",
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
      },
    ]);
  });

  // Empty as written is bad input, not an unrepresentable domain.
  it("still exits 2 on an interval that is empty as written", async () => {
    const { code, stdout, stderr } = await runMain(["check", "inverted.ts"]);
    expect(code).toBe(2);
    expect(stdout).toHaveLength(0);
    const diagnostics = stderr;
    expect(diagnostics).toHaveLength(1);
    expect(diagnostics[0]).toContain("inverted.ts:1: @ensures{backwards}:");
    expect(diagnostics[0]).toContain("empty interval");
  });
});
