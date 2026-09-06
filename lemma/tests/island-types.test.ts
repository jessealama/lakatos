import { describe, it, expect } from "vitest";
import {
  buildProbe,
  hostType,
  typable,
  type ParsedAnnotation,
} from "../src/island-types.js";
import { extractFromSource } from "../src/extract.js";
import { parsePrefix } from "../src/prefix-parser.js";
import { parseBody } from "../src/formula-parser.js";
import { EmptyAfterClampError } from "../src/range.js";
import type { ClassTable } from "../src/class-domain.js";

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
