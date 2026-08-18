import { describe, it, expect, vi, afterEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { runLean } from "../engines/thales/frontend/src/run.js";
import type { ProveVerdict } from "../src/envelope.js";

// The Lean toolchain never runs in unit tests: the runner is mocked at the
// module seam, exactly as cli-unhealthy.test.ts mocks pabst's runTests.
vi.mock("../engines/thales/frontend/src/run.js", () => ({
  runLean: vi.fn(),
  findEngineRoot: vi.fn(),
}));
const runLeanMock = vi.mocked(runLean);

const ANNOTATED = `/** @ensures{pos} forall (n: int ∈ [0, 5)) { annotated(n) >= 0 } */\nexport function annotated(n: number): number { return n; }\n`;

const verdict = (fn: string, szs: string, reason = "r"): ProveVerdict => ({
  identity: ["annotated.ts", fn, "pos"],
  szs,
  reason,
});

describe("cli prove", () => {
  useTempProject("lakatos-cli-prove-", {
    "annotated.ts": ANNOTATED,
    "plain.ts": "export const x = 1;\n",
    "invalid.ts": `class Hidden {\n  /** @ensures{p} forall (x: int) { id(x) === x } */\n  static id(x: number): number { return x; }\n}\n`,
  });

  afterEach(() => {
    runLeanMock.mockReset();
    fs.rmSync(".thales", { recursive: true, force: true });
  });

  it("healthy run: envelope from verdicts, artifact on disk, exit 0", () => {
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [verdict("annotated", "Theorem")],
    });
    const { code, stdout, stderr } = runMain(["prove", "annotated.ts"]);
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "annotated.ts",
        function: "annotated",
        property: "pos",
        szs: "Theorem",
      },
    ]);
    expect(env.seed).toBeUndefined();
    expect(env.passed).toBeUndefined();
    const artifact = path.join(".thales", "annotated.lean");
    expect(runLeanMock.mock.calls[0]![0]).toEqual([artifact]);
    expect(fs.readFileSync(artifact, "utf8")).toContain("#thales_prove");
    expect(stderr.join("\n")).toContain("transcribed 1 annotation");
  });

  it("verdict fields map through: an Inappropriate reason survives", () => {
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [
        verdict("annotated", "Inappropriate", "AwaitExpression at 2:10"),
      ],
    });
    const { code, stdout } = runMain(["prove", "annotated.ts"]);
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations[0]).toMatchObject({
      szs: "Inappropriate",
      reason: "AwaitExpression at 2:10",
    });
  });

  it("input errors join the envelope and force exit 2", () => {
    runLeanMock.mockReturnValue({ kind: "completed", verdicts: [] });
    const { code, stdout, stderr } = runMain(["prove", "invalid.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "invalid.ts",
        function: "Hidden.id",
        property: "p",
        szs: "InputError",
        error: expect.stringMatching(/^invalid\.ts:2: /),
      },
    ]);
    // No valid annotations -> no artifacts -> the prover never runs.
    expect(runLeanMock).not.toHaveBeenCalled();
    expect(stderr.join("\n")).toContain("invalid.ts:2: ");
  });

  it("no annotations at all: empty envelope, no prover run, exit 0", () => {
    runLeanMock.mockReturnValue({ kind: "completed", verdicts: [] });
    const { code, stdout } = runMain(["prove", "plain.ts"]);
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([]);
    expect(runLeanMock).not.toHaveBeenCalled();
  });

  it("no-project: NotTried envelope, message on stderr, exit 2", () => {
    runLeanMock.mockReturnValue({
      kind: "no-project",
      message: "lake was not found on PATH",
    });
    const { code, stdout, stderr } = runMain(["prove", "annotated.ts"]);
    expect(code).toBe(2);
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
    expect(stderr.join("\n")).toContain("lake was not found on PATH");
  });

  it("failed: raw output on stderr, NotTried envelope, exit 2", () => {
    runLeanMock.mockReturnValue({
      kind: "failed",
      stdout: "raw lake stdout\n",
      stderr: "raw lake stderr\n",
    });
    const writes: string[] = [];
    const writeSpy = vi
      .spyOn(process.stderr, "write")
      .mockImplementation((chunk) => {
        writes.push(String(chunk));
        return true;
      });
    try {
      const { code, stdout } = runMain(["prove", "annotated.ts"]);
      expect(code).toBe(2);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env.annotations[0].szs).toBe("NotTried");
      expect(writes.join("")).toContain("raw lake stdout");
      expect(writes.join("")).toContain("raw lake stderr");
    } finally {
      writeSpy.mockRestore();
    }
  });

  it("bad-verdicts and join mismatches surface as unhealthy exit 2", () => {
    runLeanMock.mockReturnValue({
      kind: "bad-verdicts",
      messages: ["unparseable verdict line: x"],
    });
    const bad = runMain(["prove", "annotated.ts"]);
    expect(bad.code).toBe(2);
    expect(bad.stderr.join("\n")).toContain("unparseable verdict line: x");
    expect(JSON.parse(bad.stdout[0]!).annotations[0].szs).toBe("NotTried");

    // A healthy Lean run whose verdicts do not cover the annotations is
    // just as untrustworthy.
    runLeanMock.mockReturnValue({ kind: "completed", verdicts: [] });
    const missing = runMain(["prove", "annotated.ts"]);
    expect(missing.code).toBe(2);
    expect(missing.stderr.join("\n")).toContain("no verdict for");
    const env = JSON.parse(missing.stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations[0].szs).toBe("NotTried");
  });
});
