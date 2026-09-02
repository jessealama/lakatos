import { describe, it, expect } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";

const ILL_TYPED = {
  "tsconfig.json": JSON.stringify({ include: ["src"] }),
  "src/abs.ts":
    "/** @ensures{nonNegative} forall (x: number ∈ (-∞, ∞)) { 0 <= abs(x) } */\n" +
    "export function abs(x: number): number {\n" +
    '  return "not a number at all";\n' +
    "}\n",
};

describe("refute refuses an ill-typed program", () => {
  useTempProject("lakatos-gate-refute-", ILL_TYPED);

  it("reports InputError per annotation and exits 2", () => {
    const run = runMain(["refute"]);
    expect(run.code).toBe(2);
    const joined = run.stderr.join("\n");
    expect(joined).toContain(
      "error: src/abs.ts:3: TS2322: Type 'string' is not assignable to type 'number'.",
    );
    expect(joined).toContain(
      "lakatos: the program does not type check under lakatos's required options; reporting 1 annotation as InputError",
    );
    // The gate runs before codegen: nothing was generated, no run dir named.
    expect(joined).not.toContain("generated");
    expect(run.stdout).toHaveLength(1);
    const env = JSON.parse(run.stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "src/abs.ts",
        function: "abs",
        property: "nonNegative",
        szs: "InputError",
        error:
          "the program does not type check: src/abs.ts:3: TS2322: Type 'string' is not assignable to type 'number'.",
      },
    ]);
  });
});

describe("prove refuses the same program the same way", () => {
  useTempProject("lakatos-gate-prove-", ILL_TYPED);

  it("never reaches the emitter: no arity checks, no Inappropriate", () => {
    const run = runMain(["prove"]);
    expect(run.code).toBe(2);
    const env = JSON.parse(run.stdout[0]!);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toMatchObject({ szs: "InputError" });
    expect(run.stderr.join("\n")).not.toContain("emitted");
  });
});

describe("the gate is whole-project", () => {
  useTempProject("lakatos-gate-elsewhere-", {
    "tsconfig.json": JSON.stringify({ include: ["src"] }),
    "src/good.ts":
      "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
      "export function id(n: number): number {\n  return n;\n}\n",
    "src/broken.ts": 'export const n: number = "nope";\n',
  });

  it("refuses annotations in clean files when any file is broken", () => {
    const run = runMain(["refute"]);
    expect(run.code).toBe(2);
    const env = JSON.parse(run.stdout[0]!);
    expect(env.annotations).toEqual([
      {
        file: "src/good.ts",
        function: "id",
        property: "pos",
        szs: "InputError",
        error:
          "the program does not type check: src/broken.ts:1: TS2322: Type 'string' is not assignable to type 'number'.",
      },
    ]);
  });
});

describe("several diagnostics over several annotations", () => {
  useTempProject("lakatos-gate-many-", {
    "tsconfig.json": JSON.stringify({ include: ["src"] }),
    "src/a.ts":
      "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
      "export function id(n: number): number {\n  return n;\n}\n" +
      'export const bad1: number = "one";\n',
    "src/b.ts":
      "/** @ensures{pos} forall (n: nat) { twice(n) >= 0 } */\n" +
      "export function twice(n: number): number {\n  return 2 * n;\n}\n" +
      'export const bad2: number = "two";\n',
  });

  it("names the first diagnostic and counts the rest", () => {
    const run = runMain(["refute"]);
    expect(run.code).toBe(2);
    const joined = run.stderr.join("\n");
    expect(joined).toContain(
      "lakatos: the program does not type check under lakatos's required options; reporting 2 annotations as InputError",
    );
    const env = JSON.parse(run.stdout[0]!);
    expect(env.annotations).toHaveLength(2);
    for (const a of env.annotations) {
      expect(a.szs).toBe("InputError");
      expect(a.error).toMatch(
        /^the program does not type check: src\/[ab]\.ts:5: TS2322: .* \(and 1 more\)$/,
      );
    }
    // Both diagnostics reach stderr even though only one reaches the envelope.
    expect(joined).toContain("error: src/a.ts:5: TS2322:");
    expect(joined).toContain("error: src/b.ts:5: TS2322:");
  });
});

describe("a diagnostic with no file of its own", () => {
  useTempProject("lakatos-gate-optionerr-", {
    "tsconfig.json": JSON.stringify({
      compilerOptions: { isolatedDeclarations: true },
      include: ["src"],
    }),
    "src/a.ts":
      "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
      "export function id(n: number): number {\n  return n;\n}\n",
  });

  it("formats without a file:line prefix", () => {
    const run = runMain(["refute"]);
    expect(run.code).toBe(2);
    expect(run.stderr.join("\n")).toContain("error: TS5069: Option");
    const env = JSON.parse(run.stdout[0]!);
    expect(env.annotations[0].error).toContain(
      "the program does not type check: TS5069: Option",
    );
  });
});

describe("a tsconfig that names no files", () => {
  useTempProject("lakatos-gate-noinputs-", {
    "tsconfig.json": JSON.stringify({ files: [] }),
    "src/a.ts":
      "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
      "export function id(n: number): number {\n  return n;\n}\n",
  });

  it("refuses the discovered files as outside the program", () => {
    const run = runMain(["check"]);
    expect(run.code).toBe(2);
    expect(run.stderr.join("\n")).toContain(
      "error: src/a.ts is not part of the program tsconfig.json describes",
    );
    const env = JSON.parse(run.stdout[0]!);
    expect(env.annotations).toEqual([
      expect.objectContaining({
        function: "id",
        szs: "InputError",
        error:
          "src/a.ts is not part of the program tsconfig.json describes, so it was not type checked",
      }),
    ]);
  });
});

describe("no tsconfig: the run is refused", () => {
  useTempProject(
    "lakatos-gate-missing-",
    {
      "src/a.ts":
        "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
        "export function id(n: number): number {\n  return n;\n}\n",
    },
    { tsconfig: false },
  );

  it("reports every annotation InputError and exits 2", () => {
    const run = runMain(["check"]);
    expect(run.code).toBe(2);
    expect(run.stderr.join("\n")).toContain(
      "lakatos: no tsconfig.json; reporting 1 annotation as InputError",
    );
    const env = JSON.parse(run.stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "src/a.ts",
        function: "id",
        property: "pos",
        szs: "InputError",
        error:
          "no tsconfig.json: lakatos type checks the program before analyzing it and needs the project's compiler options to do so",
      },
    ]);
    expect(fs.existsSync(".lakatos")).toBe(false);
  });
});

describe("a named file outside the program", () => {
  useTempProject("lakatos-gate-outside-", {
    "tsconfig.json": JSON.stringify({ include: ["src"] }),
    "src/a.ts":
      "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
      "export function id(n: number): number {\n  return n;\n}\n",
    "extra/b.ts":
      "/** @ensures{pos} forall (n: nat) { other(n) >= 0 } */\n" +
      "export function other(n: number): number {\n  return n;\n}\n",
  });

  it("refuses only that file's annotations and still runs the rest", () => {
    const run = runMain(["check", "src/a.ts", "extra/b.ts"]);
    expect(run.code).toBe(2);
    const env = JSON.parse(run.stdout[0]!);
    const byFile = Object.fromEntries(
      env.annotations.map((a: { file: string; szs: string }) => [
        a.file,
        a.szs,
      ]),
    );
    expect(byFile).toEqual({
      "src/a.ts": "NotTried",
      "extra/b.ts": "InputError",
    });
  });
});

describe("the project switches strict off", () => {
  useTempProject("lakatos-gate-loose-", {
    "tsconfig.json": JSON.stringify({
      compilerOptions: { strict: false },
      include: ["src"],
    }),
    "src/a.ts":
      "/** @ensures{nonNeg} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number {\n" +
      "  const y: number = undefined;\n" +
      "  return x + y;\n}\n",
  });

  it("is checked under lakatos's required options regardless", () => {
    const run = runMain(["prove"]);
    expect(run.code).toBe(2);
    expect(run.stderr.join("\n")).toContain(
      "error: src/a.ts:3: TS2322: Type 'undefined' is not assignable to type 'number'.",
    );
    expect(run.stderr.join("\n")).toContain(
      "lakatos: the program does not type check under lakatos's required options; reporting 1 annotation as InputError",
    );
    expect(JSON.parse(run.stdout[0]!).annotations[0]).toMatchObject({
      szs: "InputError",
    });
  });
});

describe("clean project under a tsconfig: no warning, no refusal", () => {
  useTempProject("lakatos-gate-clean-", {
    "tsconfig.json": JSON.stringify({ include: ["src"] }),
    "src/a.ts":
      "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
      "export function id(n: number): number {\n  return n;\n}\n",
  });

  it("says nothing about it, and leaves its build info for the next run", () => {
    const run = runMain(["check"]);
    expect(run.code).toBe(1);
    expect(run.stderr.join("\n")).not.toContain("type check");
    expect(fs.existsSync(path.join(".lakatos", "typecheck.tsbuildinfo"))).toBe(
      true,
    );
  });
});
