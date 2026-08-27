import { describe, it, expect } from "vitest";
import { typecheckProject } from "../src/typecheck.js";
import { LemmaError } from "../src/errors.js";
import { useTempProject } from "../../tests/helpers/cli.js";

describe("typecheckProject: no tsconfig.json", () => {
  useTempProject("lemma-tc-none-", {
    "src/a.ts": "export const a: number = 1;\n",
  });

  it("is skipped, not clean: there are no options to check under", () => {
    expect(typecheckProject(process.cwd())).toEqual({
      kind: "skipped",
      reason: "no-tsconfig",
    });
  });
});

describe("typecheckProject: solution-style tsconfig naming no files", () => {
  useTempProject("lemma-tc-solution-", {
    "tsconfig.json": JSON.stringify({
      files: [],
      references: [{ path: "./packages/a" }],
    }),
    "packages/a/tsconfig.json": "{}",
    "packages/a/a.ts": "export const a = 1;\n",
  });

  it("is skipped: an empty program can vouch for nothing", () => {
    expect(typecheckProject(process.cwd())).toEqual({
      kind: "skipped",
      reason: "no-inputs",
    });
  });
});

describe("typecheckProject: clean project", () => {
  useTempProject("lemma-tc-clean-", {
    "tsconfig.json": JSON.stringify({
      compilerOptions: { strict: true },
      include: ["src"],
    }),
    "src/a.ts": "export function id(x: number): number {\n  return x;\n}\n",
  });

  it("reports clean", () => {
    expect(typecheckProject(process.cwd())).toEqual({ kind: "clean" });
  });
});

describe("typecheckProject: ill-typed body (the issue's repro 1)", () => {
  useTempProject("lemma-tc-badbody-", {
    "tsconfig.json": JSON.stringify({ include: ["src"] }),
    "src/abs.ts":
      "export function abs(x: number): number {\n" +
      '  return "not a number at all";\n' +
      "}\n",
  });

  it("fails with a structured, cwd-relative, 1-indexed diagnostic", () => {
    const result = typecheckProject(process.cwd());
    expect(result.kind).toBe("failed");
    if (result.kind !== "failed") return;
    expect(result.diagnostics).toHaveLength(1);
    expect(result.diagnostics[0]).toMatchObject({
      file: "src/abs.ts",
      line: 2,
      code: 2322,
    });
    expect(result.diagnostics[0]!.message).toContain("not assignable");
  });
});

describe("typecheckProject: error outside the annotated file", () => {
  useTempProject("lemma-tc-elsewhere-", {
    "tsconfig.json": JSON.stringify({ include: ["src"] }),
    "src/good.ts": "export function id(x: number): number {\n  return x;\n}\n",
    "src/broken.ts": 'export const n: number = "nope";\n',
  });

  it("fails: the checker's unit is the program, not the file", () => {
    const result = typecheckProject(process.cwd());
    expect(result.kind).toBe("failed");
    if (result.kind !== "failed") return;
    expect(result.diagnostics.map((d) => d.file)).toEqual(["src/broken.ts"]);
  });
});

describe("typecheckProject: version-skew compiler option", () => {
  useTempProject("lemma-tc-skew-", {
    "tsconfig.json": JSON.stringify({
      compilerOptions: { someFutureFlag: true },
      include: ["src"],
    }),
    "src/a.ts": "export const a: number = 1;\n",
  });

  it("ignores option diagnostics, same as discovery does", () => {
    expect(typecheckProject(process.cwd())).toEqual({ kind: "clean" });
  });
});

describe("typecheckProject: malformed tsconfig", () => {
  useTempProject("lemma-tc-garbage-", {
    "tsconfig.json": "{ not json",
    "src/a.ts": "export const a = 1;\n",
  });

  it("throws the same LemmaError shape discovery throws", () => {
    expect(() => typecheckProject(process.cwd())).toThrow(LemmaError);
    expect(() => typecheckProject(process.cwd())).toThrow(/^tsconfig\.json:/);
  });
});
