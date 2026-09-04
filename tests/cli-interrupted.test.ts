import { describe, it, expect, vi, afterEach } from "vitest";
import * as fs from "node:fs";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { main } from "../src/cli.js";
import { runTests } from "../engines/pabst/src/run.js";
import { runEmission } from "../engines/thales/frontend/src/run.js";
import { RUN_ROOT } from "../src/run-dir.js";

// An interrupted run still honors the output contract: one schema-valid
// envelope on stdout in which every annotation the engine was to evaluate
// reports User, and the documented exit 2. Both engines are mocked at the
// same module seams cli-unhealthy and cli-prove use, so no signal is sent
// here; tests/interrupt-e2e.test.ts covers the real thing.
vi.mock("../engines/pabst/src/run.js", () => ({ runTests: vi.fn() }));
vi.mock("../engines/thales/frontend/src/run.js", () => ({
  runEmission: vi.fn(),
  findEngineRoot: vi.fn(),
}));
const runTestsMock = vi.mocked(runTests);
const runEmissionMock = vi.mocked(runEmission);

describe("cli on an interrupted run", () => {
  useTempProject("lakatos-cli-interrupted-", {
    "annotated.ts": [
      "/** @ensures{pos} forall (n: int ∈ [0, 5)) { annotated(n) >= 0 } */",
      "export function annotated(n: number): number { return n; }",
      "",
      "/** @ensures{same} forall (n: int ∈ [0, 5)) { twin(n) === n } */",
      "export function twin(n: number): number { return n; }",
      "",
    ].join("\n"),
    "lone.ts": [
      "/** @ensures{pos} forall (n: int ∈ [0, 5)) { lone(n) >= 0 } */",
      "export function lone(n: number): number { return n; }",
      "",
    ].join("\n"),
    "invalid.ts": [
      "class Hidden {",
      "  /** @ensures{p} forall (x: int ∈ [0, 5)) { id(x) === x } */",
      "  static id(x: number): number { return x; }",
      "}",
      "",
    ].join("\n"),
  });

  afterEach(() => {
    runTestsMock.mockReset();
    runEmissionMock.mockReset();
    fs.rmSync(RUN_ROOT, { recursive: true, force: true });
  });

  it("refute: every annotation User, one diagnostic, exit 2", async () => {
    runTestsMock.mockReturnValue({ kind: "interrupted", signal: "SIGINT" });
    const { code, stdout, stderr } = await runMain(["refute", "annotated.ts"]);
    expect(code).toBe(2);
    expect(stdout).toHaveLength(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "annotated.ts",
        function: "annotated",
        property: "pos",
        szs: "User",
        reason: "the run was interrupted (SIGINT)",
      },
      {
        file: "annotated.ts",
        function: "twin",
        property: "same",
        szs: "User",
        reason: "the run was interrupted (SIGINT)",
      },
    ]);
    expect(stderr).toContain(
      "lakatos: interrupted by SIGINT; reporting 2 annotations as User",
    );
  });

  it("refute: counts the lone annotation in the singular", async () => {
    runTestsMock.mockReturnValue({ kind: "interrupted", signal: "SIGINT" });
    const { stderr } = await runMain(["refute", "lone.ts"]);
    expect(stderr).toContain(
      "lakatos: interrupted by SIGINT; reporting 1 annotation as User",
    );
  });

  it("refute: an interrupted run reports no test counts", async () => {
    runTestsMock.mockReturnValue({ kind: "interrupted", signal: "SIGTERM" });
    const { stdout } = await runMain(["refute", "annotated.ts"]);
    const env = JSON.parse(stdout[0]!);
    // The seed and the generated count were known before the engine ran;
    // passed/failed only a completed vitest could have told us.
    expect(env.generated).toBe(2);
    expect(Number.isInteger(env.seed)).toBe(true);
    expect(env.passed).toBeUndefined();
    expect(env.failed).toBeUndefined();
  });

  it("refute: input errors keep their own status beside the User entries", async () => {
    runTestsMock.mockReturnValue({ kind: "interrupted", signal: "SIGHUP" });
    const { code, stdout } = await runMain([
      "refute",
      "annotated.ts",
      "invalid.ts",
    ]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    const statuses = env.annotations.map(
      (a: { szs: string }) => a.szs,
    ) as string[];
    expect(statuses.filter((s) => s === "User")).toHaveLength(2);
    expect(statuses).toContain("InputError");
  });

  it("refute: the envelope is printed while the guard still stands", async () => {
    // A user who presses Ctrl-C twice would otherwise kill lakatos in the
    // gap between the engine's death and the report — the very failure the
    // User status exists to prevent — so the guard must outlast the run.
    runTestsMock.mockReturnValue({ kind: "interrupted", signal: "SIGINT" });
    const outside = process.listenerCount("SIGINT");
    let atPrint = outside;
    const logSpy = vi.spyOn(console, "log").mockImplementation(() => {
      atPrint = process.listenerCount("SIGINT");
    });
    const errSpy = vi.spyOn(console, "error").mockImplementation(() => {});
    try {
      expect(await main(["refute", "annotated.ts"])).toBe(2);
    } finally {
      logSpy.mockRestore();
      errSpy.mockRestore();
    }
    expect(atPrint).toBe(outside + 1);
    expect(process.listenerCount("SIGINT")).toBe(outside);
  });

  it("refute: a signal that reached lakatos reports User even when the engine exited by status", async () => {
    // vitest catches SIGINT and exits 130 rather than dying of it, so the
    // child's death says nothing; the signal reached lakatos too, and that
    // is what the run reads.
    runTestsMock.mockImplementation(() => {
      process.kill(process.pid, "SIGINT");
      return { kind: "no-results", status: 130, stdout: "", stderr: "" };
    });
    const { code, stdout, stderr } = await runMain(["refute", "annotated.ts"]);
    expect(code).toBe(2);
    expect(stdout).toHaveLength(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(
      env.annotations.map((a: { szs: string; reason?: string }) => [
        a.szs,
        a.reason,
      ]),
    ).toEqual([
      ["User", "the run was interrupted (SIGINT)"],
      ["User", "the run was interrupted (SIGINT)"],
    ]);
    expect(stderr).toContain(
      "lakatos: interrupted by SIGINT; reporting 2 annotations as User",
    );
    expect(stderr.join("\n")).not.toContain("error:");
  });

  it("prove: a signal that reached lakatos outranks a completed Lean run", async () => {
    runEmissionMock.mockImplementation(() => {
      process.kill(process.pid, "SIGTERM");
      return { kind: "failed", stdout: "", stderr: "" };
    });
    const { code, stdout, stderr } = await runMain(["prove", "annotated.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(
      env.annotations.every((a: { szs: string }) => a.szs === "User"),
    ).toBe(true);
    expect(stderr).toContain(
      "lakatos: interrupted by SIGTERM; reporting 2 annotations as User",
    );
  });

  it("prove: the same contract through the Lean runner", async () => {
    runEmissionMock.mockReturnValue({ kind: "interrupted", signal: "SIGINT" });
    const { code, stdout, stderr } = await runMain(["prove", "annotated.ts"]);
    expect(code).toBe(2);
    expect(stdout).toHaveLength(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(
      env.annotations.every((a: { szs: string }) => a.szs === "User"),
    ).toBe(true);
    expect(stderr).toContain(
      "lakatos: interrupted by SIGINT; reporting 2 annotations as User",
    );
  });
});
