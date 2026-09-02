import { describe, it, expect, vi } from "vitest";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";

// Behind the gate no valid program makes the frontend classify Error, so
// the only way to exercise that exit code is to make the emitter report one.
vi.mock("../engines/thales/frontend/src/run.js", () => ({
  runLean: vi.fn(),
  runEmission: vi.fn(),
  findEngineRoot: vi.fn(),
}));
vi.mock(
  "../engines/thales/frontend/src/emission-artifacts.js",
  async (importOriginal) => {
    const actual =
      await importOriginal<
        typeof import("../engines/thales/frontend/src/emission-artifacts.js")
      >();
    return {
      ...actual,
      writeEmissionArtifacts: (files: string[], outRoot: string) =>
        actual.writeEmissionArtifacts(files, outRoot).map((a) => ({
          ...a,
          leanFile: undefined,
          classified: a.annotations.map((annotation) => ({
            annotation,
            szs: "Error" as const,
            reason: "the typed walk broke an invariant",
          })),
        })),
    };
  },
);

describe("cli prove: a frontend Error is an engine failure", () => {
  useTempProject("lakatos-cli-classified-error-", {
    "a.ts":
      "/** @ensures{pos} forall (n: int ∈ [0, 5)) { f(n) >= 0 } */\n" +
      "export function f(n: number): number {\n  return n;\n}\n",
  });

  it("ships the verdict in `error` and exits 2", () => {
    const { code, stdout } = runMain(["prove", "a.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "a.ts",
        function: "f",
        property: "pos",
        szs: "Error",
        error: "the typed walk broke an invariant",
      },
    ]);
  });
});
