import { describe, it, expect } from "vitest";
import {
  buildProbe,
  hostType,
  typable,
  typeFormulas,
  type IslandTyping,
  type ParsedAnnotation,
  type ParsedFile,
} from "../src/island-types.js";
import { extract, extractFromSource } from "../src/extract.js";
import { parsePrefix } from "../src/prefix-parser.js";
import { parseBody } from "../src/formula-parser.js";
import { EmptyAfterClampError } from "../src/range.js";
import { typecheckProject } from "../src/typecheck.js";
import { annotationKey } from "../src/qualified-name.js";
import type { ClassTable } from "../src/class-domain.js";
import { useTempProject } from "../../tests/helpers/cli.js";

/** Parse every annotation of a module the way the CLI does. */
function annotationsOf(src: string, file = "m.ts") {
  const r = extractFromSource(src, file);
  const annotations: ParsedAnnotation[] = r.annotations.map((raw) => {
    try {
      const { binders, body } = parsePrefix(raw.formula);
      return { raw, parsed: { binders, formula: parseBody(body) } };
    } catch (e) {
      if (e instanceof EmptyAfterClampError) return { raw };
      throw e;
    }
  });
  return { ...r, annotations };
}

function bindersOf(prefix: string) {
  return parsePrefix(`${prefix} { true }`).binders;
}

describe("hostType", () => {
  it("binds int and nat at number, the other primitives at themselves, a class at its name", () => {
    const [i, n, x, b, s, g, p] = bindersOf(
      "forall (i: int) (n: nat) (x: number) (b: boolean) (s: string) (g: bigint) (p: Point)",
    );
    expect([i, n, x, b, s, g, p].map((v) => hostType(v!))).toEqual([
      "number",
      "number",
      "number",
      "boolean",
      "string",
      "bigint",
      "Point",
    ]);
  });
});

const POINT =
  "export class Point {\n" +
  "  constructor(readonly x: number) {}\n" +
  "  get norm(): number { return Math.abs(this.x); }\n" +
  "}\n";

describe("buildProbe", () => {
  it("appends one arrow per annotation with each atom on its own line under satisfies boolean", () => {
    const src =
      POINT +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) (q: Point) { f(x) ≡ x ∧ q.norm >= 0 } */\n" +
      "export function f(x: number): number { return x; }\n";
    const m = annotationsOf(src);
    const probe = buildProbe(src, m.annotations, m.classes);
    expect(probe.text.startsWith(src)).toBe(true);
    expect(probe.text.slice(src.length)).toBe(
      "\n// lakatos island typing probes; never written to disk\n" +
        "void ((x: number, q: Point): void => {\n" +
        "  (Object.is(f(x), x)) satisfies boolean;\n" +
        "  (q.norm >= 0) satisfies boolean;\n" +
        "});\n",
    );
    expect(probe.atoms).toHaveLength(2);
    expect(probe.atoms.map((s) => probe.text.slice(s.start, s.end))).toEqual([
      "(Object.is(f(x), x))",
      "(q.norm >= 0)",
    ]);
    expect(probe.atoms.map((s) => [s.annotation, s.atom])).toEqual([
      [0, 0],
      [0, 1],
    ]);
    expect(probe.probes).toHaveLength(1);
    expect(
      probe.atoms.every((s) => s.probeStart === probe.probes[0]!.start),
    ).toBe(true);
    expect(
      probe.text.slice(probe.probes[0]!.start, probe.probes[0]!.end),
    ).toMatch(/^void \(\(x: number, q: Point\): void => \{\n[\s\S]*\}\);\n$/);
  });

  it("skips an annotation with no parse and one whose class binder is not a declared class, keeping indices", () => {
    const src =
      "/** @ensures{a} forall (x: int ∈ [1000000000000000000000000000000, 10000000000000000000000000000000]) { f(x) > 0 } */\n" +
      "/** @ensures{b} forall (q: Nope) { f(1) > 0 } */\n" +
      "/** @ensures{c} forall (x: int) { f(x) > 0 } */\n" +
      "export function f(x: number): number { return x; }\n";
    const m = annotationsOf(src);
    expect(m.annotations[0]!.parsed).toBeUndefined();
    const probe = buildProbe(src, m.annotations, m.classes);
    expect(probe.probes.map((p) => p.annotation)).toEqual([2]);
    expect(probe.atoms.map((s) => s.annotation)).toEqual([2]);
    expect(probe.text.slice(src.length)).not.toContain("Nope");
  });
});

describe("typable", () => {
  const classes: ClassTable = new Map([
    ["Point", { exported: true, defaultExport: false, ctorParams: [] }],
  ]);
  const withPrefix = (prefix: string): ParsedAnnotation => ({
    raw: { propertyName: "p", functionName: "f", formula: "", line: 1 },
    parsed: { binders: bindersOf(prefix), formula: parseBody("true") },
  });

  it("is true for primitives and declared classes, false otherwise", () => {
    expect(typable(withPrefix("forall (x: int)"), classes)).toBe(true);
    expect(typable(withPrefix("forall (p: Point)"), classes)).toBe(true);
    expect(typable(withPrefix("forall (p: Nope)"), classes)).toBe(false);
    expect(
      typable(
        { raw: { propertyName: "p", functionName: "f", formula: "", line: 1 } },
        classes,
      ),
    ).toBe(false);
  });
});

/** A file of the current project, extracted and parsed like the CLI does. */
function parsedFile(file: string): ParsedFile {
  const r = extract(file);
  return {
    file,
    exports: r.exports,
    classes: r.classes,
    annotations: r.annotations.map((raw) => {
      try {
        const { binders, body } = parsePrefix(raw.formula);
        return { raw, parsed: { binders, formula: parseBody(body) } };
      } catch (e) {
        if (e instanceof EmptyAfterClampError) return { raw };
        throw e;
      }
    }),
  };
}

/** Gate the current project and type the named files' formulas. */
function typing(...files: string[]): IslandTyping {
  const check = typecheckProject(process.cwd());
  if (check.kind !== "clean")
    throw new Error(`fixture is not clean: ${check.kind}`);
  return typeFormulas(files.map(parsedFile), check.checked);
}

const SCALE =
  "export function scale(x: number, factor: number): number {\n" +
  "  return x * factor;\n" +
  "}\n";

describe("typeFormulas: the issue's three repros", () => {
  useTempProject("lemma-island-repros-", {
    "j.ts":
      SCALE +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { scale(x) >= 0 } */\n" +
      "export function id(x: number): number {\n  return x;\n}\n",
    "q.ts":
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) + q >= 0 } */\n" +
      "export function f(x: number): number {\n  return x;\n}\n",
    "b.ts":
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { h(x) } */\n" +
      "export function h(x: number): number {\n  return x;\n}\n",
  });

  it("names the atom and carries tsc's diagnostic", () => {
    const t = typing("j.ts", "q.ts", "b.ts");
    expect(t.invalid).toEqual([
      {
        file: "j.ts",
        invalid: [
          {
            propertyName: "p",
            functionName: "id",
            line: 4,
            message:
              "@ensures{p}: in atom `scale(x) >= 0`: TS2554: Expected 2 arguments, but got 1.",
          },
        ],
      },
      {
        file: "q.ts",
        invalid: [
          {
            propertyName: "p",
            functionName: "f",
            line: 1,
            message:
              "@ensures{p}: in atom `f(x) + q >= 0`: TS2304: Cannot find name 'q'.",
          },
        ],
      },
      {
        file: "b.ts",
        invalid: [
          {
            propertyName: "p",
            functionName: "h",
            line: 1,
            message:
              "@ensures{p}: in atom `h(x)`: TS1360: Type 'number' does not satisfy the expected type 'boolean'.",
          },
        ],
      },
    ]);
    expect([...t.refused].sort()).toEqual(
      [
        annotationKey("b.ts", { functionName: "h", propertyName: "p" }),
        annotationKey("j.ts", { functionName: "id", propertyName: "p" }),
        annotationKey("q.ts", { functionName: "f", propertyName: "p" }),
      ].sort(),
    );
  });
});

describe("typeFormulas: attribution and skipping", () => {
  useTempProject("lemma-island-attr-", {
    "two.ts":
      SCALE +
      "export function h(x: number): number { return x; }\n" +
      "/** @ensures{both} forall (x: int ∈ [0, 5)) { scale(x) >= 0 ∧ h(x) } */\n" +
      "/** @ensures{fine} forall (x: int ∈ [0, 5)) { scale(x, 2) >= 0 } */\n" +
      "/** @ensures{empty} forall (x: int ∈ [1000000000000000000000000000000, 10000000000000000000000000000000]) { h(x) > 0 } */\n" +
      "/** @ensures{unknown} forall (q: Nope) { h(1) > 0 } */\n" +
      "export function id(x: number): number { return x; }\n",
    "pt.ts":
      "export class Point {\n" +
      "  constructor(readonly x: number) {}\n" +
      "  get norm(): number { return Math.abs(this.x); }\n" +
      "}\n" +
      "/** @ensures{ok} forall (p: Point) { p.norm >= 0 } */\n" +
      "/** @ensures{bad} forall (p: Point) { p.nope >= 0 } */\n" +
      "export function f(p: Point): number { return p.norm; }\n",
  });

  it("joins every faulty atom of one annotation in source order, and leaves sound and untypable siblings alone", () => {
    const t = typing("two.ts");
    expect(t.invalid).toEqual([
      {
        file: "two.ts",
        invalid: [
          {
            propertyName: "both",
            functionName: "id",
            line: 5,
            message:
              "@ensures{both}: in atom `scale(x) >= 0`: TS2554: Expected 2 arguments, but got 1.; " +
              "in atom `h(x)`: TS1360: Type 'number' does not satisfy the expected type 'boolean'.",
          },
        ],
      },
    ]);
    expect(t.refused).toEqual(
      new Set([
        annotationKey("two.ts", { functionName: "id", propertyName: "both" }),
      ]),
    );
  });

  it("types a class binder at its class", () => {
    const t = typing("pt.ts");
    expect(t.invalid).toEqual([
      {
        file: "pt.ts",
        invalid: [
          {
            propertyName: "bad",
            functionName: "f",
            line: 6,
            message:
              "@ensures{bad}: in atom `p.nope >= 0`: TS2339: Property 'nope' does not exist on type 'Point'.",
          },
        ],
      },
    ]);
  });
});

describe("typeFormulas: the project's own unused-declaration checks", () => {
  useTempProject("lemma-island-unused-", {
    "tsconfig.json": JSON.stringify({
      compilerOptions: {
        target: "es2022",
        module: "nodenext",
        types: [],
        noUnusedLocals: true,
        noUnusedParameters: true,
      },
      include: ["**/*.ts"],
    }),
    "u.ts":
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { one() > 0 } */\n" +
      "export function one(): number { return 1; }\n",
  });

  it("do not fire against the probe's scaffolding", () => {
    const t = typing("u.ts");
    expect(t.invalid).toEqual([]);
    expect(t.refused.size).toBe(0);
  });
});

describe("typeFormulas: nothing to type", () => {
  it("returns empty without a program", () => {
    expect(typeFormulas([], undefined)).toEqual({
      invalid: [],
      refused: new Set(),
    });
  });

  it("refuses to type without the gate's program", () => {
    const file: ParsedFile = {
      file: "x.ts",
      exports: new Set(["f"]),
      classes: new Map(),
      annotations: [
        {
          raw: { propertyName: "p", functionName: "f", formula: "", line: 1 },
          parsed: {
            binders: bindersOf("forall (x: int)"),
            formula: parseBody("f(x) > 0"),
          },
        },
      ],
    };
    expect(() => typeFormulas([file], undefined)).toThrow(/gate's program/);
  });
});

describe("typeFormulas: free identifiers are exports or standard globals", () => {
  useTempProject("lemma-island-free-", {
    "helper.ts": "export function g(x: number): number { return x; }\n",
    "hidden.ts":
      "function g(x: number): number { return x; }\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { g(x) > 0 } */\n" +
      "export function f(x: number): number { return x; }\n",
    "imported.ts":
      'import { g } from "./helper.js";\n' +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { g(x) > 0 } */\n" +
      "export function f(x: number): number { return x + g(x); }\n",
    "reexported.ts":
      'import { g } from "./helper.js";\n' +
      "export { g };\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { g(x) >= 0 } */\n" +
      "export function f(x: number): number { return x; }\n",
    "fine.ts":
      "export const x = 3;\n" +
      "/** @ensures{shadow} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "/** @ensures{globals} forall (x: int ∈ [0, 5)) { Math.abs(f(x)) >= 0 ∧ Number.isFinite(f(x)) } */\n" +
      "/** @ensures{callback} forall (x: int ∈ [0, 5)) { [f(x)].every((y) => y >= 0) } */\n" +
      "/** @ensures{undef} forall (x: int ∈ [0, 5)) { f(x) !== undefined } */\n" +
      "export function f(x: number): number { return x; }\n",
    "twice.ts":
      "function g(x: number): number { return x; }\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { g(x) > 0 ∧ g(x) + g(x) > 0 } */\n" +
      "export function f(x: number): number { return x; }\n",
  });

  it("refuses a name declared in the module but not exported", () => {
    const t = typing("hidden.ts");
    expect(t.invalid).toEqual([
      {
        file: "hidden.ts",
        invalid: [
          {
            propertyName: "p",
            functionName: "f",
            line: 2,
            message:
              "@ensures{p}: in atom `g(x) > 0`: 'g' is not exported from hidden.ts; " +
              "a formula may name only the module's exports and the host's standard globals",
          },
        ],
      },
    ]);
    expect(t.refused).toEqual(
      new Set([
        annotationKey("hidden.ts", { functionName: "f", propertyName: "p" }),
      ]),
    );
  });

  it("refuses an imported name the module does not re-export, and accepts one it does", () => {
    expect(typing("imported.ts").invalid[0]!.invalid[0]!.message).toBe(
      "@ensures{p}: in atom `g(x) > 0`: 'g' is not exported from imported.ts; " +
        "a formula may name only the module's exports and the host's standard globals",
    );
    expect(typing("reexported.ts")).toEqual({
      invalid: [],
      refused: new Set(),
    });
  });

  it("accepts binders, standard globals, a callback's own parameter, and undefined", () => {
    expect(typing("fine.ts")).toEqual({ invalid: [], refused: new Set() });
  });

  it("names an offender once per atom", () => {
    expect(typing("twice.ts").invalid[0]!.invalid[0]!.message).toBe(
      "@ensures{p}: in atom `g(x) > 0`: 'g' is not exported from twice.ts; " +
        "a formula may name only the module's exports and the host's standard globals; " +
        "in atom `g(x) + g(x) > 0`: 'g' is not exported from twice.ts; " +
        "a formula may name only the module's exports and the host's standard globals",
    );
  });
});
