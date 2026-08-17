import { describe, it, expect, vi, afterEach } from "vitest";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { runTests } from "../engines/pabst/src/run.js";

// The output contract holds even when the underlying vitest run is
// unhealthy: one schema-valid envelope on stdout (every annotation
// NotTried — generated but never evaluated), diagnostics on stderr, and
// exit 2. Both unhealthy RunResult kinds are pinned by mocking runTests.
vi.mock("../engines/pabst/src/run.js", () => ({ runTests: vi.fn() }));
const runTestsMock = vi.mocked(runTests);

describe("cli refute on unhealthy runs", () => {
  useTempProject("lakatos-cli-unhealthy-", {
    "annotated.ts": `/** @ensures{pos} forall (n: nat) { annotated(n) >= 0 } */\nexport function annotated(n: number): number { return n; }\n`,
  });

  afterEach(() => {
    runTestsMock.mockReset();
  });

  it("no-results: prints a NotTried envelope, raw output on stderr, exit 2", () => {
    runTestsMock.mockReturnValue({
      kind: "no-results",
      status: 137,
      stdout: "raw vitest stdout\n",
      stderr: "raw vitest stderr\n",
    });
    const writes: string[] = [];
    const writeSpy = vi
      .spyOn(process.stderr, "write")
      .mockImplementation((chunk) => {
        writes.push(String(chunk));
        return true;
      });
    try {
      const { code, stdout } = runMain(["refute", "annotated.ts"]);
      expect(code).toBe(2);
      expect(stdout).toHaveLength(1);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env.annotations).toEqual([
        {
          file: "annotated.ts",
          function: "annotated",
          property: "pos",
          szs: "NotTried",
        },
      ]);
      expect(env.generated).toBe(1);
      expect(Number.isInteger(env.seed)).toBe(true);
      expect(writes.join("")).toContain("raw vitest stdout");
      expect(writes.join("")).toContain("raw vitest stderr");
    } finally {
      writeSpy.mockRestore();
    }
  });

  it("broken-run: prints a NotTried envelope, error lines on stderr, exit 2", () => {
    runTestsMock.mockReturnValue({
      kind: "broken-run",
      status: 1,
      messages: ["Cannot find module 'lakatos/runtime'"],
    });
    const { code, stdout, stderr } = runMain(["refute", "annotated.ts"]);
    expect(code).toBe(2);
    expect(stdout).toHaveLength(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "annotated.ts",
        function: "annotated",
        property: "pos",
        szs: "NotTried",
      },
    ]);
    expect(stderr).toContain(
      "error: Cannot find module 'lakatos/runtime'",
    );
  });
});
