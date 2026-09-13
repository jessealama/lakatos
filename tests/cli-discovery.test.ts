import { describe, it, expect } from "vitest";
import { runMain, useTempProject } from "./helpers/cli.js";

describe("cli zero-argument discovery", () => {
  describe("with a src/ directory and no tsconfig", () => {
    useTempProject(
      "lakatos-cli-zerosrc-",
      {
        "src/qux.ts": `/** @ensures{pos} forall (n: nat) { qux(n) >= 0 } */\nexport function qux(n: number): number { return n; }\n`,
        "src/types.d.ts": `export declare function qux(n: number): number;\n`,
      },
      { tsconfig: false },
    );

    it("does not scan src/: discovery stops before any envelope", async () => {
      const { code, stdout, stderr } = await runMain(["check"]);
      expect(code).toBe(2);
      expect(stderr).toEqual([
        'error: no tsconfig.json to discover sources from; pass files or globs (e.g. lakatos refute "src/**/*.ts")',
      ]);
      expect(stdout).toHaveLength(0);
    });
  });

  describe("with a tsconfig.json", () => {
    useTempProject("lakatos-cli-zerotsc-", {
      "tsconfig.json": JSON.stringify({ include: ["lib"] }),
      "lib/qux.ts": `/** @ensures{pos} forall (n: nat) { qux(n) >= 0 } */\nexport function qux(n: number): number { return n; }\n`,
      "src/decoy.ts": `export function decoy(): number { return 1; }\n`,
    });

    it("discovers via tsconfig.json, ignoring src/", async () => {
      const { code, stdout, stderr } = await runMain(["check"]);
      expect(code).toBe(1);
      expect(stderr[0]).toBe(
        "lakatos: no files given; discovered 1 file(s) via tsconfig.json",
      );
      expect(JSON.parse(stdout[0]!).annotations).toHaveLength(1);
    });
  });

  describe("with a malformed tsconfig.json", () => {
    useTempProject("lakatos-cli-zerobad-", {
      "tsconfig.json": JSON.stringify({ extends: "./missing.json" }),
      "src/a.ts": `export const a = 1;\n`,
    });

    it("exits 2 with the tsconfig diagnostic, not falling through", async () => {
      const { code, stderr } = await runMain(["check"]);
      expect(code).toBe(2);
      expect(stderr).toHaveLength(1);
      expect(stderr[0]).toContain("error: tsconfig.json:");
    });
  });
});
