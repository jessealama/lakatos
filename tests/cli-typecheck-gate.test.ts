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
      "lakatos: the program does not type check; reporting 1 annotation as InputError",
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
      "lakatos: the program does not type check; reporting 2 annotations as InputError",
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

  it("warns and proceeds: an empty program vouches for nothing", () => {
    const run = runMain(["check"]);
    expect(run.code).toBe(1);
    expect(run.stderr.join("\n")).toContain(
      "lakatos: tsconfig.json names no files; skipping type check",
    );
    const env = JSON.parse(run.stdout[0]!);
    expect(env.annotations[0]).toMatchObject({ szs: "NotTried" });
  });
});

describe("no tsconfig: the run proceeds unchecked, with a warning", () => {
  useTempProject("lakatos-gate-warn-", {
    "src/a.ts":
      "/** @ensures{pos} forall (n: nat) { id(n) >= 0 } */\n" +
      "export function id(n: number): number {\n  return n;\n}\n",
  });

  it("warns once and still runs (check stub: NotTried, exit 1)", () => {
    const run = runMain(["check"]);
    expect(run.code).toBe(1);
    expect(run.stderr.join("\n")).toContain(
      "lakatos: no tsconfig.json; skipping type check",
    );
    const env = JSON.parse(run.stdout[0]!);
    expect(env.annotations[0]).toMatchObject({ szs: "NotTried" });
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
