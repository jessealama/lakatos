import { describe, it, expect, vi, afterEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { announcedRunDir, runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { runEmission } from "../engines/thales/frontend/src/run.js";
import type { ProveVerdict } from "../src/envelope.js";
import type { ProveStatus } from "../src/szs.js";
import { RUN_ROOT } from "../src/run-dir.js";

// The plain-Lean emission pipeline through the CLI spine, which prove runs
// by default — nothing needs selecting. The engine is mocked at the same
// module seam cli-prove.test.ts uses; the containment, interrupt, and health
// contracts must match the transcriber spine's, exit codes included.
vi.mock("../engines/thales/frontend/src/run.js", () => ({
  runLean: vi.fn(),
  runEmission: vi.fn(),
  findEngineRoot: vi.fn(),
}));
const runEmissionMock = vi.mocked(runEmission);

const verdict = (
  file: string,
  fn: string,
  property: string,
  szs: ProveStatus,
): ProveVerdict => ({ identity: [file, fn, property], szs, reason: "r" });

describe("cli prove, plain pipeline", () => {
  useTempProject("lakatos-cli-prove-plain-", {
    "annotated.ts": `/** @ensures{pos} forall (n: int ∈ [0, 5)) { annotated(n) >= 0 } */\nexport function annotated(n: number): number { return n; }\n`,
    "other.ts": `/** @ensures{pos} forall (n: int ∈ [0, 5)) { other(n) >= 0 } */\nexport function other(n: number): number { return n; }\n`,
    "mixed.ts": [
      "/** @ensures{big} forall (n: int ∈ [0, 1000000000000000000000000000000]) { huge(n) >= 0 } */",
      "export function huge(n: number): number { return n; }",
      "",
      "/** @ensures{pos} forall (n: int ∈ [0, 5)) { small(n) >= 0 } */",
      "export function small(n: number): number { return n; }",
      "",
    ].join("\n"),
    "consts.ts": [
      "const double = (x: number): number => x * 2;",
      "/** @ensures{pos} forall (n: int ∈ [0, 4)) { applyDouble(n) >= 0 } */",
      "export function applyDouble(n: number): number {",
      "  return double(n);",
      "}",
      "",
    ].join("\n"),
    "classbinder.ts": [
      "export class Box { constructor(readonly size: number) {} }",
      "/** @ensures{p} forall (b: Box) { volume(b) >= 0 } */",
      "export function volume(b: Box): number { return b.size; }",
      "",
    ].join("\n"),
    "unregistered.ts": [
      "/** @ensures{pos} forall (n: int ∈ [0, 4)) { caller(n) >= 0 } */",
      "export function caller(n: number): number { return mystery(n); }",
      "",
    ].join("\n"),
  });

  afterEach(() => {
    runEmissionMock.mockReset();
    fs.rmSync(RUN_ROOT, { recursive: true, force: true });
  });

  it("healthy run: classified and proved annotations merge, exit 0", () => {
    runEmissionMock.mockReturnValue({
      kind: "completed",
      verdicts: [verdict("mixed.ts", "small", "pos", "Theorem")],
      failures: [],
      diagnostics: [],
    });
    const { code, stdout, stderr } = runMain(["prove", "mixed.ts"]);
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
    // The emission JSON is the run's artifact; only mappable declarations
    // reach it.
    const emission = JSON.parse(
      fs.readFileSync(
        path.join(announcedRunDir(stderr), "thales", "mixed.ts.json"),
        "utf8",
      ),
    );
    expect(emission.declarations.map((d: { name: string }) => d.name)).toEqual([
      "huge",
      "small",
    ]);
    expect(emission.obligations).toHaveLength(1);
  });

  it("a fully classified file never reaches the engine", () => {
    const { code, stdout } = runMain(["prove", "consts.ts", "classbinder.ts"]);
    expect(runEmissionMock).not.toHaveBeenCalled();
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual(
      expect.arrayContaining([
        {
          file: "consts.ts",
          function: "applyDouble",
          property: "pos",
          szs: "Inappropriate",
          reason:
            "'applyDouble' could not be modeled: 'double' could not be modeled: " +
            "unmapped TypeScript construct 'VariableStatement' at 1:7",
        },
        {
          file: "classbinder.ts",
          function: "volume",
          property: "p",
          szs: "Inappropriate",
          reason: "class-valued binder 'Box' is not yet modeled",
        },
      ]),
    );
    expect(env.annotations).toHaveLength(2);
  });

  it("a frontend-classified engine failure reports Error in the envelope's error field", () => {
    const { code, stdout } = runMain(["prove", "unregistered.ts"]);
    expect(runEmissionMock).not.toHaveBeenCalled();
    // A per-annotation Error verdict is a healthy run, exactly as it is
    // when the old pipeline's elaborator reports it.
    expect(code).toBe(0);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "unregistered.ts",
        function: "caller",
        property: "pos",
        szs: "Error",
        error:
          "'caller' could not be modeled: no model registered for 'mystery'",
      },
    ]);
  });

  it("a contained file failure: Error entries for that file, siblings verdict, exit 2", () => {
    runEmissionMock.mockImplementation((jobs) => {
      const other = jobs.find((j) => j.leanFile.endsWith("other.ts.lean"))!;
      return {
        kind: "completed",
        verdicts: [verdict("annotated.ts", "annotated", "pos", "Theorem")],
        failures: [
          {
            file: other.leanFile,
            messages: [
              `thales-emit failed on ${other.jsonFile} before rendering the artifact`,
            ],
          },
        ],
        diagnostics: [],
      };
    });
    const { code, stdout } = runMain(["prove", "annotated.ts", "other.ts"]);
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
  });

  it("an unhealthy join: all NotTried, exit 2", () => {
    runEmissionMock.mockReturnValue({
      kind: "completed",
      verdicts: [
        verdict("annotated.ts", "annotated", "pos", "Theorem"),
        verdict("annotated.ts", "phantom", "pos", "Theorem"),
      ],
      failures: [],
      diagnostics: [],
    });
    const { code, stdout } = runMain(["prove", "annotated.ts"]);
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
  });

  it("an interrupted run reports User for everything planned, exit 2", () => {
    runEmissionMock.mockReturnValue({ kind: "interrupted", signal: "SIGINT" });
    const { code, stdout } = runMain(["prove", "annotated.ts", "mixed.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual(
      expect.arrayContaining([
        {
          file: "annotated.ts",
          function: "annotated",
          property: "pos",
          szs: "User",
          reason: "the run was interrupted (SIGINT)",
        },
        {
          file: "mixed.ts",
          function: "small",
          property: "pos",
          szs: "User",
          reason: "the run was interrupted (SIGINT)",
        },
        // The frontend settled this one before the engine ran; the
        // interrupt does not unsettle it.
        {
          file: "mixed.ts",
          function: "huge",
          property: "big",
          szs: "NotTried",
          kind: "unsupported-range",
          reason:
            "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
        },
      ]),
    );
    expect(env.annotations).toHaveLength(3);
  });

  it("no Lean engine: NotTried envelope, exit 2", () => {
    runEmissionMock.mockReturnValue({
      kind: "no-project",
      message: "the Lean proof engine is not part of this installation",
    });
    const { code, stdout } = runMain(["prove", "annotated.ts"]);
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
  });
});
