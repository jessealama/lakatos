import { describe, it, expect, vi, afterEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { announcedRunDir, runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { runLean } from "../engines/thales/frontend/src/run.js";
import type { ProveVerdict } from "../src/envelope.js";
import type { ProveStatus } from "../src/szs.js";
import { RUN_ROOT } from "../src/run-dir.js";

// The Lean toolchain never runs in unit tests: the runner is mocked at the
// module seam, exactly as cli-unhealthy.test.ts mocks pabst's runTests.
vi.mock("../engines/thales/frontend/src/run.js", () => ({
  runLean: vi.fn(),
  findEngineRoot: vi.fn(),
}));
const runLeanMock = vi.mocked(runLean);

const ANNOTATED = `/** @ensures{pos} forall (n: int ∈ [0, 5)) { annotated(n) >= 0 } */\nexport function annotated(n: number): number { return n; }\n`;

const verdict = (fn: string, szs: ProveStatus, reason = "r"): ProveVerdict => ({
  identity: ["annotated.ts", fn, "pos"],
  szs,
  reason,
});

describe("cli prove", () => {
  useTempProject("lakatos-cli-prove-", {
    "annotated.ts": ANNOTATED,
    "other.ts": `/** @ensures{pos} forall (n: int ∈ [0, 5)) { other(n) >= 0 } */\nexport function other(n: number): number { return n; }\n`,
    "plain.ts": "export const x = 1;\n",
    "allhuge.ts": `/** @ensures{big} forall (n: int ∈ [0, 1000000000000000000000000000000]) { lone(n) >= 0 } */\nexport function lone(n: number): number { return n; }\n`,
    "mixed.ts": [
      "/** @ensures{big} forall (n: int ∈ [0, 1000000000000000000000000000000]) { huge(n) >= 0 } */",
      "export function huge(n: number): number { return n; }",
      "",
      "/** @ensures{pos} forall (n: int ∈ [0, 5)) { small(n) >= 0 } */",
      "export function small(n: number): number { return n; }",
      "",
    ].join("\n"),
    "invalid.ts": `class Hidden {\n  /** @ensures{p} forall (x: int) { id(x) === x } */\n  static id(x: number): number { return x; }\n}\n`,
    "classbinder.ts": [
      "export class Box { constructor(readonly size: number) {} }",
      "/** @ensures{p} forall (b: Box) { volume(b) >= 0 } */",
      "export function volume(b: Box): number { return b.size; }",
      "",
    ].join("\n"),
  });

  afterEach(() => {
    runLeanMock.mockReset();
    fs.rmSync(RUN_ROOT, { recursive: true, force: true });
  });

  it("healthy run: envelope from verdicts, artifact on disk, exit 0", () => {
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [verdict("annotated", "Theorem")],
      failures: [],
      diagnostics: [],
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
        axioms: [],
      },
    ]);
    expect(env.seed).toBeUndefined();
    expect(env.passed).toBeUndefined();
    // The run's artifacts live under the directory named by the instant the
    // envelope reports, so a report and its artifacts match by eye.
    const artifact = path.join(
      announcedRunDir(stderr),
      "thales",
      "annotated.ts.lean",
    );
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
      failures: [],
      diagnostics: [],
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

  it("a refuted property ships falsified and exits 1, like refute", () => {
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [
        {
          ...verdict("annotated", "CounterSatisfiable"),
          counterexample: { n: 0 },
        },
      ],
      failures: [],
      diagnostics: [],
    });
    const { code, stdout } = runMain(["prove", "annotated.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations[0]).toMatchObject({
      szs: "CounterSatisfiable",
      kind: "falsified",
      counterexample: { n: 0 },
    });
  });

  it("an unsupported range ships NotTried with kind and reason; the rest still prove", () => {
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [
        { identity: ["mixed.ts", "small", "pos"], szs: "Theorem", reason: "r" },
      ],
      failures: [],
      diagnostics: [],
    });
    const { code, stdout } = runMain(["prove", "mixed.ts"]);
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual(
      expect.arrayContaining([
        {
          file: "mixed.ts",
          function: "huge",
          property: "big",
          szs: "NotTried",
          kind: "unsupported-range",
          reason:
            "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
        },
        {
          file: "mixed.ts",
          function: "small",
          property: "pos",
          szs: "Theorem",
          axioms: [],
        },
      ]),
    );
    expect(env.annotations).toHaveLength(2);
  });

  it("a file whose only annotation is untried never reaches Lean", () => {
    const { code, stdout, stderr } = runMain(["prove", "allhuge.ts"]);
    expect(runLeanMock).not.toHaveBeenCalled();
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "allhuge.ts",
        function: "lone",
        property: "big",
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
      },
    ]);
    // The artifact is still written: it documents the skip as a comment.
    const artifact = fs.readFileSync(
      path.join(announcedRunDir(stderr), "thales", "allhuge.ts.lean"),
      "utf8",
    );
    expect(artifact).toContain("-- not tried");
  });

  it("a class-valued binder reports Inappropriate without reaching Lean", () => {
    const { code, stdout, stderr } = runMain(["prove", "classbinder.ts"]);
    expect(runLeanMock).not.toHaveBeenCalled();
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "classbinder.ts",
        function: "volume",
        property: "p",
        szs: "Inappropriate",
        reason: "class-valued binder 'Box' is not yet modeled",
      },
    ]);
    // The artifact is still written: it documents the refusal as a comment.
    const artifact = fs.readFileSync(
      path.join(announcedRunDir(stderr), "thales", "classbinder.ts.lean"),
      "utf8",
    );
    expect(artifact).toContain("-- inappropriate");
  });

  it("an unhealthy run keeps the unsupported-range metadata", () => {
    runLeanMock.mockReturnValue({
      kind: "failed",
      stdout: "",
      stderr: "",
    });
    const { code, stdout } = runMain(["prove", "mixed.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual(
      expect.arrayContaining([
        {
          file: "mixed.ts",
          function: "huge",
          property: "big",
          szs: "NotTried",
          kind: "unsupported-range",
          reason:
            "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
        },
        {
          file: "mixed.ts",
          function: "small",
          property: "pos",
          szs: "NotTried",
        },
      ]),
    );
    expect(env.annotations).toHaveLength(2);
  });

  it("input errors join the envelope and force exit 2", () => {
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [],
      failures: [],
      diagnostics: [],
    });
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
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [],
      failures: [],
      diagnostics: [],
    });
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

  it("join mismatches surface as unhealthy exit 2", () => {
    // A healthy Lean run whose verdicts do not cover the annotations is
    // untrustworthy: it indicates a transcriber or engine bug.
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [],
      failures: [],
      diagnostics: [],
    });
    const missing = runMain(["prove", "annotated.ts"]);
    expect(missing.code).toBe(2);
    expect(missing.stderr.join("\n")).toContain("no verdict for");
    const env = JSON.parse(missing.stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations[0].szs).toBe("NotTried");
  });

  it("a contained file failure: Error entries for that file, others verdict, exit 2", () => {
    // The failure is keyed by the artifact the run was actually handed: its
    // directory is named after this invocation, unknown to the test upfront.
    runLeanMock.mockImplementation((files) => {
      const other = files.find((f) => f.endsWith("other.ts.lean"))!;
      return {
        kind: "completed",
        verdicts: [verdict("annotated", "Theorem")],
        failures: [
          {
            file: other,
            messages: [
              `the Lean run on ${other} failed before reporting its verdicts`,
            ],
          },
        ],
        diagnostics: [],
      };
    });
    const { code, stdout, stderr } = runMain([
      "prove",
      "annotated.ts",
      "other.ts",
    ]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual(
      expect.arrayContaining([
        {
          file: "annotated.ts",
          function: "annotated",
          property: "pos",
          szs: "Theorem",
          axioms: [],
        },
        {
          file: "other.ts",
          function: "other",
          property: "pos",
          szs: "Error",
          error:
            "the Lean run on this file's artifact failed before reporting its verdicts",
        },
      ]),
    );
    expect(env.annotations).toHaveLength(2);
    expect(stderr.join("\n")).toContain("failed before reporting its verdicts");
  });

  it("Lean diagnostics pass through to stderr on a healthy run", () => {
    runLeanMock.mockReturnValue({
      kind: "completed",
      verdicts: [verdict("annotated", "Theorem")],
      failures: [],
      diagnostics: ["note: some linter chatter"],
    });
    const { code, stderr } = runMain(["prove", "annotated.ts"]);
    expect(code).toBe(0);
    expect(stderr.join("\n")).toContain("note: some linter chatter");
  });
});
