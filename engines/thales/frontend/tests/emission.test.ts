import { assert, describe, expect, test } from "vitest";
import * as fs from "node:fs";
import { schemaValidator } from "../../../../tests/helpers/schema-validator.js";
import {
  type EmitClass,
  type EmitDecl,
  type EmitExpr,
  type EmitFunction,
  type EmitStmt,
  emitModule,
} from "../src/emission.js";
import { annotationKey, LemmaError } from "../../../../lemma/src/index.js";

/** A declaration's own name. A residual site is named by its owner and
 * index, so a list assertion stays total rather than hiding one. */
function declName(d: EmitDecl): string {
  return d.kind === "residual" ? `${d.owner}#residual_${d.site}` : d.name;
}

/** A function declaration's body, narrowed out of the declaration union. */
function fnBody(d: EmitDecl): EmitStmt[] {
  assert(d.kind === "function");
  return d.body;
}

const FIXTURE = "engines/thales/tests/fixtures/tracer.ts";
const read = () => fs.readFileSync(FIXTURE, "utf8");

const expectValidEmission = schemaValidator(
  new URL("../../../../schemas/thales-emission.schema.json", import.meta.url),
  "emission",
);

describe("emitModule on the tracer fixture", () => {
  test("maps add with its body IR", () => {
    const { emission } = emitModule(read(), FIXTURE);
    expect(emission.file).toBe(FIXTURE);
    expect(emission.declarations).toEqual([
      {
        kind: "function",
        name: "add",
        params: [
          { name: "a", type: "number" },
          { name: "b", type: "number" },
        ],
        source: expect.stringContaining("export function add"),
        body: [
          {
            kind: "return",
            expr: {
              kind: "binop",
              op: "+",
              left: { kind: "id", name: "a" },
              right: { kind: "id", name: "b" },
            },
          },
        ],
      },
    ]);
  });

  test("structures the commutes obligation", () => {
    const { emission } = emitModule(read(), FIXTURE);
    expect(emission.obligations).toEqual([
      {
        function: "add",
        property: "commutes",
        formula:
          "forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) }",
        payload: {
          kind: "structured",
          binders: [
            { name: "a", kind: "range", lo: "0", hi: "10" },
            { name: "b", kind: "range", lo: "0", hi: "10" },
          ],
          conclusion: {
            kind: "eq",
            left: {
              kind: "call",
              callee: "add",
              args: [
                { kind: "id", name: "a" },
                { kind: "id", name: "b" },
              ],
            },
            right: {
              kind: "call",
              callee: "add",
              args: [
                { kind: "id", name: "b" },
                { kind: "id", name: "a" },
              ],
            },
          },
        },
      },
    ]);
  });

  test("classifies the two degraded annotations with old-pipeline reasons", () => {
    const { classified } = emitModule(read(), FIXTURE);
    expect(
      classified.map((c) => [c.annotation.propertyName, c.szs, c.reason]),
    ).toEqual([
      [
        "nonNegative",
        "Inappropriate",
        "'fetchTotal' could not be modeled: unmapped TypeScript construct 'AsyncKeyword' at 9:8",
      ],
      [
        "bumps",
        "Inappropriate",
        "'Counter#bump' could not be modeled: class 'Counter' has no constructor implementation to model",
      ],
    ]);
  });

  test.each([
    ["engines/thales/tests/fixtures/tracer.ts"],
    ["engines/thales/tests/fixtures/statements.ts"],
    ["engines/thales/tests/fixtures/binders.ts"],
    ["engines/thales/tests/fixtures/degradations.ts"],
    ["engines/thales/tests/fixtures/classes.ts"],
    ["engines/thales/tests/fixtures/class-params.ts"],
    ["engines/thales/tests/fixtures/module-consts.ts"],
    ["engines/thales/tests/fixtures/nested-class-binder.ts"],
    ["engines/thales/tests/fixtures/unions.ts"],
    ["engines/thales/tests/fixtures/optionals.ts"],
    ["engines/thales/tests/fixtures/defaults.ts"],
    ["engines/thales/tests/fixtures/ctor-defaults.ts"],
    ["engines/thales/tests/fixtures/instance-defaults.ts"],
    ["engines/thales/tests/fixtures/object-is-tagged.ts"],
    ["engines/thales/tests/fixtures/fields.ts"],
    [
      "engines/thales/tests/conformance/theorem/class-binder-equality-guards.ts",
    ],
    ["engines/thales/tests/conformance/theorem/boolean-classes.ts"],
  ])("the emission for %s validates against the schema", (fixture) => {
    expectValidEmission(
      emitModule(fs.readFileSync(fixture, "utf8"), fixture).emission,
    );
  });

  test.each([
    ["engines/thales/tests/fixtures/tracer.ts", "tracer.emission.json"],
    ["engines/thales/tests/fixtures/operators.ts", "operators.emission.json"],
    ["engines/thales/tests/fixtures/statements.ts", "statements.emission.json"],
    ["engines/thales/tests/fixtures/binders.ts", "binders.emission.json"],
    [
      "engines/thales/tests/fixtures/degradations.ts",
      "degradations.emission.json",
    ],
    ["engines/thales/tests/fixtures/classes.ts", "classes.emission.json"],
    [
      "engines/thales/tests/fixtures/class-params.ts",
      "class-params.emission.json",
    ],
    [
      "engines/thales/tests/fixtures/module-consts.ts",
      "module-consts.emission.json",
    ],
    [
      "engines/thales/tests/fixtures/nested-class-binder.ts",
      "nested-class-binder.emission.json",
    ],
    ["engines/thales/tests/fixtures/unions.ts", "unions.emission.json"],
    ["engines/thales/tests/fixtures/optionals.ts", "optionals.emission.json"],
    ["engines/thales/tests/fixtures/defaults.ts", "defaults.emission.json"],
    [
      "engines/thales/tests/fixtures/ctor-defaults.ts",
      "ctor-defaults.emission.json",
    ],
    [
      "engines/thales/tests/fixtures/instance-defaults.ts",
      "instance-defaults.emission.json",
    ],
    [
      "engines/thales/tests/fixtures/object-is-tagged.ts",
      "object-is-tagged.emission.json",
    ],
    ["engines/thales/tests/fixtures/fields.ts", "fields.emission.json"],
    [
      "engines/thales/tests/conformance/theorem/class-binder-equality-guards.ts",
      "class-binder-equality-guards.emission.json",
    ],
    [
      "engines/thales/tests/conformance/theorem/boolean-classes.ts",
      "boolean-classes.emission.json",
    ],
  ])(
    "the pinned emission for %s is exactly what the frontend emits",
    (fixture, pin) => {
      const pinned = JSON.parse(
        fs.readFileSync(`engines/thales/tests/fixtures/${pin}`, "utf8"),
      );
      expect(
        emitModule(fs.readFileSync(fixture, "utf8"), fixture).emission,
      ).toEqual(pinned);
    },
  );

  test("every stacked JSDoc block's @ensures becomes its own obligation", () => {
    const fixture =
      "engines/thales/tests/conformance/theorem/stacked-blocks.ts";
    const { emission } = emitModule(fs.readFileSync(fixture, "utf8"), fixture);
    expect(emission.obligations.map((o) => o.property)).toEqual([
      "nonNegative",
      "atLeastOne",
    ]);
  });

  test("extraction results ride along", () => {
    const { annotations, invalid } = emitModule(read(), FIXTURE);
    expect(annotations.map((a) => a.propertyName)).toEqual([
      "commutes",
      "nonNegative",
      "bumps",
    ]);
    expect(invalid).toEqual([]);
  });
});

/** The classification for one annotated declaration. */
function classifiedOf(decl: string, fn = "f"): string | undefined {
  const src = `/** @ensures{p} forall (x: int ∈ [0, 5)) { ${fn}(x) ≡ x } */\n${decl}\n`;
  return emitModule(src, "t.ts").classified[0]?.reason;
}

test("a free function's defaulted parameter models", () => {
  expect(
    classifiedOf("export function f(x: number = 0): number { return x; }"),
  ).toBeUndefined();
});

/** The payload of one obligation on a mappable identity function. */
function payloadOf(formula: string) {
  const src = `/** @ensures{p} ${formula} */\nexport function f(x: number): number {\n  return x;\n}\n`;
  const { emission, classified } = emitModule(src, "t.ts");
  expect(classified).toEqual([]);
  return emission.obligations[0]!.payload;
}

describe("signature and body blockers", () => {
  test.each([
    [
      "an async function",
      "async function f(x: number): number { return x; }",
      undefined,
    ],
    ["a generator", "function* f(x: number): number { return x; }", undefined],
    [
      "a destructured parameter",
      "function f({ x }: { x: number }): number { return 1; }",
      "ObjectBindingPattern",
    ],
    [
      "a rest parameter",
      "function f(...x: number[]): number { return 1; }",
      "DotDotDotToken",
    ],
    [
      "a required parameter after an optional one",
      "function f(x?: number, y: number): number { return 1; }",
      undefined,
    ],
    ["an untyped parameter", "function f(x): number { return 1; }", undefined],
    [
      "a non-number parameter type",
      "function f(x: string): number { return 1; }",
      "StringKeyword",
    ],
    [
      "a bodiless overload signature",
      "function f(x: number): number;",
      undefined,
    ],
    [
      "a non-number return type",
      'function f(x: number): string { return "x"; }',
      "StringKeyword",
    ],
    [
      "a loop in the body",
      "function f(x: number): number { while (x < 1) { x = 1; } return x; }",
      "WhileStatement",
    ],
    [
      "a bare return",
      "function f(x: number): number { return; }",
      "ReturnStatement",
    ],
  ])("%s classifies its annotation", (_label, decl, construct) => {
    const reason = classifiedOf(decl);
    expect(reason).toMatch(
      /'f' could not be modeled: unmapped TypeScript construct/,
    );
    if (construct !== undefined) expect(reason).toContain(`'${construct}'`);
  });

  test.each([
    ["the left operand", "return (await g()) + x;"],
    ["the right operand", "return x + (await g());"],
    ["a call argument", "return g2(await g());"],
  ])("a blocker in %s records its construct at the site", (_label, body) => {
    const src =
      "export function g2(y: number): number { return y; }\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      `export function f(x: number): number { ${body} }\n`;
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(/^unmapped TypeScript construct 'AwaitExpression'/),
    ]);
  });

  test("a static class member classifies under its dotted name", () => {
    const src = [
      "export class Box {",
      "  /** @ensures{p} forall (x: int ∈ [0, 5)) { make(x) ≡ x } */",
      "  static make(x: number): number {",
      "    return x;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toMatch(
      /'Box\.make' could not be modeled: class 'Box' has no constructor/,
    );
  });

  test("nameless and computed-name declarations bind no blocker", () => {
    const src = [
      "export default function (x: number): number { return x; }",
      "export default class {}",
      'class C { ["m"](x: number): number { return x; } }',
      "interface I { x: number; }",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(emission.declarations).toEqual([]);
    expect(classified).toEqual([]);
  });
});

describe("obligation payload degradations", () => {
  test.each([
    ["a half-bounded range", "forall (x: int ∈ (-∞, 10]) { f(x) ≡ x }"],
    [
      "an atom that is not valid JavaScript",
      "forall (x: int ∈ [0, 5)) { f(x) is wonderful }",
    ],
    [
      "a half-bounded floor above zero",
      "forall (x: int ∈ [3, ∞)) { f(x) ≡ x }",
    ],
    ["a biconditional", "forall (x: int ∈ [0, 5)) { f(x) >= 0 ↔ x >= 0 }"],
    [
      "a nested implication under a connective",
      "forall (x: int ∈ [0, 5)) { (x > 0 → f(x) > 0) ∨ x === 0 }",
    ],
    [
      "an unparseable guard atom",
      "forall (x: int ∈ [0, 5)) { 2x >= 0 -> f(x) >= 0 }",
    ],
    ["a bigint binder", "forall (b: bigint) { f(b) ≡ b }"],
  ])("%s degrades to a bare payload", (_label, formula) => {
    expect(payloadOf(formula)).toEqual({ kind: "bare" });
  });

  test("a prefix the parser rejects escapes as the parser's own error", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number {\n  return x;\n}\n";
    expect(() => emitModule(src, "t.ts")).toThrow(LemmaError);
  });

  test("a body the formula parser rejects escapes as the parser's own error", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 && f(x) <= 9 } */\n" +
      "export function f(x: number): number {\n  return x;\n}\n";
    expect(() => emitModule(src, "t.ts")).toThrow("∧ for conjunction");
  });

  test("an atom the formula parser rejects escapes as the parser's own error", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { 2x ≡ x } */\n" +
      "export function f(x: number): number {\n  return x;\n}\n";
    expect(() => emitModule(src, "t.ts")).toThrow("cannot parse atom");
  });

  test.each([
    [
      "an unbounded int binder",
      "forall (x: int) { f(x) ≡ x }",
      { name: "x", kind: "int" },
    ],
    [
      "an int binder over the whole line",
      "forall (x: int ∈ (-∞, ∞)) { f(x) ≡ x }",
      { name: "x", kind: "int" },
    ],
    [
      "an unbounded nat binder",
      "forall (x: nat) { f(x) ≡ x }",
      { name: "x", kind: "nat" },
    ],
    [
      "an int binder denoting the naturals",
      "forall (x: int ∈ [0, ∞)) { f(x) ≡ x }",
      { name: "x", kind: "nat" },
    ],
    [
      "a nat binder with only a ceiling",
      "forall (x: nat ∈ (-∞, 10]) { f(x) ≡ x }",
      { name: "x", kind: "range", lo: "0", hi: "11" },
    ],
  ])("%s structures", (_label, formula, binder) => {
    expect(payloadOf(formula)).toMatchObject({
      kind: "structured",
      binders: [binder],
    });
  });

  test("a guard chain structures with guards outermost first", () => {
    const src = [
      "/** @ensures{guarded} forall (x: int ∈ [0, 10)) { x >= 1 -> keep(x) >= 1 } */",
      "export function keep(x: number): number {",
      "  if (x < 1) {",
      "    return 1;",
      "  }",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "guarded.ts");
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.guards).toEqual([
      {
        kind: "binop",
        op: ">=",
        left: { kind: "id", name: "x" },
        right: { kind: "num", lit: "1" },
      },
    ]);
    expect(payload.conclusion.kind).toBe("istrue");
  });

  test("a two-guard chain keeps both antecedents in order", () => {
    const payload = payloadOf(
      "forall (x: int ∈ [0, 10)) { x >= 1 -> x >= 2 -> f(x) >= 2 }",
    );
    assert(payload.kind === "structured");
    expect(payload.guards).toEqual([
      {
        kind: "binop",
        op: ">=",
        left: { kind: "id", name: "x" },
        right: { kind: "num", lit: "1" },
      },
      {
        kind: "binop",
        op: ">=",
        left: { kind: "id", name: "x" },
        right: { kind: "num", lit: "2" },
      },
    ]);
  });

  test("a guardless payload carries no guards field", () => {
    expect(
      payloadOf("forall (x: int ∈ [0, 5)) { f(x) ≡ x }"),
    ).not.toHaveProperty("guards");
  });

  test("bounded and unbounded binders nest in order", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) (x: int) { f(a) ≡ f(x) } */\n" +
      "export function f(x: number): number { return x; }\n";
    const { emission } = emitModule(src, "t.ts");
    expect(emission.obligations[0]!.payload).toMatchObject({
      kind: "structured",
      binders: [
        { name: "a", kind: "range", lo: "0", hi: "5" },
        { name: "x", kind: "int" },
      ],
    });
  });
});

describe("boolean binders (#354)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("a boolean binder lowers to its own kind and binds at boolean", () => {
    const { emission, classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) (b: boolean) { pick(n, b) >= 0 } */\n` +
        `export function pick(n: number, b: boolean): number {\n` +
        `  if (b) {\n    return n;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual({
      kind: "structured",
      binders: [
        { name: "n", kind: "range", lo: "0", hi: "10" },
        { name: "b", kind: "boolean" },
      ],
      conclusion: {
        kind: "istrue",
        expr: {
          kind: "binop",
          op: ">=",
          left: {
            kind: "call",
            callee: "pick",
            args: [
              { kind: "id", name: "n" },
              { kind: "id", name: "b" },
            ],
          },
          right: { kind: "num", lit: "0" },
        },
      },
    });
  });

  test("a boolean binder is an island on its own and an equality side", () => {
    const { emission, classified } = emit(
      `/** @ensures{alone} forall (b: boolean) { flip(b) === !b } */\n` +
        `/** @ensures{negated} forall (b: boolean) { flip(flip(b)) === b } */\n` +
        `export function flip(b: boolean): boolean {\n  return !b;\n}\n`,
    );
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toMatchObject({
      binders: [{ name: "b", kind: "boolean" }],
      conclusion: {
        kind: "istrue",
        expr: {
          kind: "jsval-eq",
          semantics: "strict",
          left: {
            kind: "inject",
            tag: "boolean",
            expr: { kind: "call", callee: "flip" },
          },
          right: {
            kind: "inject",
            tag: "boolean",
            expr: { kind: "unop", op: "!" },
          },
        },
      },
    });
  });

  test("a boolean binder at a number position is the walk's type error", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (b: boolean) { f(b) >= 0 } */\n` +
        `export function f(n: number): number {\n  return n;\n}\n`,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        reason: expect.stringContaining(
          "identifier 'b' is a boolean, not a number",
        ),
      }),
    ]);
  });

  test("a defaulted boolean parameter opens by projecting the boolean tag", () => {
    const { emission, classified } = emit(
      `export function f(n: number, b: boolean = false): number {\n` +
        `  if (b) {\n    return n;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.params[1]).toEqual({ name: "b", type: ["boolean", "undefined"] });
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "b",
      type: "boolean",
      init: {
        kind: "cond",
        cond: {
          kind: "jsval-eq",
          semantics: "strict",
          left: { kind: "id", name: "b" },
          right: { kind: "inject", tag: "undefined" },
        },
        then: { kind: "bool", value: false },
        else: {
          kind: "project",
          tag: "boolean",
          expr: { kind: "id", name: "b" },
        },
      },
    });
  });
});

describe("unary operators", () => {
  test("'!' refuses where a number is expected", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return !(x < 1); }\n";
    const { classified } = emitModule(src, "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "'f' could not be modeled: operator '!' yields a boolean, not a number",
      ],
    ]);
  });

  test("unary minus over a non-literal is a unop node", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return -x; }\n";
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: { kind: "unop", op: "-", operand: { kind: "id", name: "x" } },
      },
    ]);
  });

  test("unary plus keeps its identity model", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return +x; }\n";
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: { kind: "unop", op: "+", operand: { kind: "id", name: "x" } },
      },
    ]);
  });

  test("unary minus structures inside a formula atom", () => {
    expect(
      payloadOf("forall (x: int ∈ [0, 5)) { f(-x) ≡ f(-x) }"),
    ).toMatchObject({
      kind: "structured",
      conclusion: {
        kind: "eq",
        left: {
          kind: "call",
          callee: "f",
          args: [{ kind: "unop", op: "-", operand: { kind: "id", name: "x" } }],
        },
      },
    });
  });

  test("parenthesized arguments and negative literals structure", () => {
    expect(payloadOf("forall (x: int ∈ [0, 5)) { f((x)) ≡ f(-1) }")).toEqual({
      kind: "structured",
      binders: [{ name: "x", kind: "range", lo: "0", hi: "5" }],
      conclusion: {
        kind: "eq",
        left: { kind: "call", callee: "f", args: [{ kind: "id", name: "x" }] },
        right: {
          kind: "call",
          callee: "f",
          args: [{ kind: "num", lit: "-1" }],
        },
      },
    });
  });
});

describe("number binders", () => {
  test.each([
    [
      "finite mixed openness",
      "(a: number ∈ (0, 1])",
      {
        name: "a",
        kind: "number",
        lower: { op: "<", lit: "0" },
        upper: { op: "<=", lit: "1" },
      },
    ],
    [
      "one-sided above zero",
      "(sf: number ∈ (0, ∞))",
      {
        name: "sf",
        kind: "number",
        lower: { op: "<", lit: "0" },
        upper: { op: "<", lit: "Infinity" },
      },
    ],
    [
      "both infinite",
      "(c: number ∈ (-∞, ∞))",
      {
        name: "c",
        kind: "number",
        lower: { op: "<", lit: "-Infinity" },
        upper: { op: "<", lit: "Infinity" },
      },
    ],
    ["no range at all", "(x: number)", { name: "x", kind: "number" }],
    [
      "closed at both ends",
      "(c: number ∈ [-100, 100])",
      {
        name: "c",
        kind: "number",
        lower: { op: "<=", lit: "-100" },
        upper: { op: "<=", lit: "100" },
      },
    ],
    [
      "open at -0 below, which IEEE comparison cannot exclude",
      "(z: number ∈ (-0, 1))",
      {
        name: "z",
        kind: "number",
        lower: { op: "<=", lit: "-0" },
        upper: { op: "<", lit: "1" },
      },
    ],
    [
      "open at 0 above, which IEEE comparison cannot exclude",
      "(w: number ∈ (-1, 0))",
      {
        name: "w",
        kind: "number",
        lower: { op: "<", lit: "-1" },
        upper: { op: "<=", lit: "0" },
      },
    ],
  ])("a number binder structures: %s", (_label, binder, expected) => {
    const src = [
      `/** @ensures{p} forall ${binder} { f(${expected.name}) >= 0 } */`,
      "export function f(x: number): number { return x * x; }",
    ].join("\n");
    const { emission, classified } = emitModule(src, "number-binders.ts");
    // A number binder is no degradation: nothing may be classified away.
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    expect(payload.kind).toBe("structured");
    assert(payload.kind === "structured");
    expect(payload.binders[0]).toEqual(expected);
    expectValidEmission(emission);
  });

  test("a multi-name number binder expands to one binder per name", () => {
    const src = [
      "/** @ensures{p} forall (x y: number) (sf: number ∈ (0, ∞)) { f(x) <= f(y) } */",
      "export function f(x: number): number { return x * x; }",
    ].join("\n");
    const { emission, classified } = emitModule(src, "number-binders.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toMatchObject({
      kind: "structured",
      binders: [
        { name: "x", kind: "number" },
        { name: "y", kind: "number" },
        {
          name: "sf",
          kind: "number",
          lower: { op: "<", lit: "0" },
          upper: { op: "<", lit: "Infinity" },
        },
      ],
    });
  });
});

describe("emitModule degradations beyond the tracer", () => {
  test("an istrue conclusion structures as istrue", () => {
    const src = [
      "/** @ensures{nonneg} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */",
      "export function f(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "f.ts");
    expect(emission.obligations[0]!.payload).toEqual({
      kind: "structured",
      binders: [{ name: "x", kind: "range", lo: "0", hi: "5" }],
      conclusion: {
        kind: "istrue",
        expr: {
          kind: "binop",
          op: ">=",
          left: {
            kind: "call",
            callee: "f",
            args: [{ kind: "id", name: "x" }],
          },
          right: { kind: "num", lit: "0" },
        },
      },
    });
  });
});

/** All classifications of a module, as [szs, reason] pairs, plus how many
 * obligations survived to emission. */
function classifications(src: string) {
  const { classified, emission } = emitModule(src, "t.ts");
  return {
    classified: classified.map((c) => [c.szs, c.reason]),
    obligations: emission.obligations.length,
  };
}

/** What an expression-level refusal now produces: the annotation is tried,
 * and the construct is recorded at its site instead of classifying the
 * declaration. Returns the constructs in source order. */
function residualConstructs(src: string, file = "t.ts"): string[] {
  const { emission, classified } = emitModule(src, file);
  expect(classified).toEqual([]);
  return emission.declarations.flatMap((d) =>
    d.kind === "residual" ? [d.construct] : [],
  );
}

/** The owners of a module's residuals, in emission order. */
function residualOwners(src: string, file = "t.ts"): string[] {
  return emitModule(src, file).emission.declarations.flatMap((d) =>
    d.kind === "residual" ? [d.owner] : [],
  );
}

/** The site numbers of a module's residuals, in emission order. */
function residualSites(src: string, file = "t.ts"): number[] {
  return emitModule(src, file).emission.declarations.flatMap((d) =>
    d.kind === "residual" ? [d.site] : [],
  );
}

const fnWith = (body: string) =>
  `/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n` +
  `export function f(x: number): number { return ${body}; }\n`;

const formulaWith = (formula: string) =>
  `/** @ensures{p} ${formula} */\n` +
  `export function f(x: number): number { return x; }\n`;

describe("body classification", () => {
  test("an overload signature does not shadow its implementation", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number;\n" +
      "export function f(x: number): number { return x; }\n";
    expect(classifications(src)).toEqual({ classified: [], obligations: 1 });
  });

  test("statements after a return never reach the artifact", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return x; return q; }\n";
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      { kind: "return", expr: { kind: "id", name: "x" } },
    ]);
  });

  test("a body that can run off the end degrades", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number {}\n";
    expect(classifications(src)).toEqual({
      classified: [
        [
          "Error",
          "'f' could not be modeled: the body must return on every path",
        ],
      ],
      obligations: 0,
    });
  });

  test("an expression past the first return is never reached", () => {
    // The lowering ends at the first return, so the dead `x.y` contributes
    // no site and the live call is what the declaration answers for.
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return g(x); return x.y; }\n";
    expect(classifications(src).classified).toEqual([
      ["Error", "'f' could not be modeled: no model registered for 'g'"],
    ]);
  });

  test("a statement kind past the first return still refuses", () => {
    // The statement scan reads the whole tree, dead arms included, so a
    // statement outside the slice degrades wherever it sits.
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return x; for (;;) {} }\n";
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        expect.stringMatching(
          /^'f' could not be modeled: unmapped TypeScript construct 'ForStatement'/,
        ),
      ],
    ]);
  });

  test("** is not supported, by name", () => {
    expect(classifications(fnWith("x ** 2"))).toEqual({
      classified: [],
      obligations: 1,
    });
    expect(residualConstructs(fnWith("x ** 2"))).toEqual([
      "'**' is not supported",
    ]);
  });

  test.each(["&", "|", "<<", "??", "=="])(
    "an operator outside the model names itself: %s",
    (op) => {
      expect(classifications(fnWith(`x ${op} 2`))).toEqual({
        classified: [],
        obligations: 1,
      });
      expect(residualConstructs(fnWith(`x ${op} 2`))).toEqual([
        `'${op}' is not supported`,
      ]);
    },
  );

  test("an unsupported operator in dead code neither refuses nor sites", () => {
    // Unreachable code cannot bear on the property, and nothing past the
    // first return reaches the artifact, so there is nothing to stand for.
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return x; return x & 7; }\n";
    expect(classifications(src)).toEqual({ classified: [], obligations: 1 });
    expect(residualConstructs(src)).toEqual([]);
  });

  test("an unsupported operator and an opaque construct site in tree order", () => {
    const prop = expect.stringMatching(
      /^unmapped TypeScript construct 'PropertyAccessExpression' at 2:\d+$/,
    );
    expect(residualConstructs(fnWith("x ** 2 + x.y"))).toEqual([
      "'**' is not supported",
      prop,
    ]);
    expect(residualSites(fnWith("x ** 2 + x.y"))).toEqual([1, 2]);
    expect(residualConstructs(fnWith("x.y + x ** 2"))).toEqual([
      prop,
      "'**' is not supported",
    ]);
    expect(residualSites(fnWith("x.y + x ** 2"))).toEqual([1, 2]);
  });

  test("an operator with no model is outside the model", () => {
    expect(classifications(fnWith("x & 7"))).toEqual({
      classified: [],
      obligations: 1,
    });
    expect(residualConstructs(fnWith("x & 7"))).toEqual([
      "'&' is not supported",
    ]);
  });

  test("a comparison in number position reports the type mismatch", () => {
    expect(classifications(fnWith("(x < 1) + 1")).classified).toEqual([
      [
        "Error",
        "'f' could not be modeled: operator '<' yields a boolean, not a number",
      ],
    ]);
  });

  test("a comparison as the returned value reports the type mismatch", () => {
    expect(classifications(fnWith("x < 1")).classified).toEqual([
      [
        "Error",
        "'f' could not be modeled: operator '<' yields a boolean, not a number",
      ],
    ]);
  });

  test("an unbound identifier fails the declaration", () => {
    expect(classifications(fnWith("y")).classified).toEqual([
      ["Error", "'f' could not be modeled: unbound identifier 'y'"],
    ]);
  });

  test("a call to a later declaration finds no model", () => {
    const src =
      fnWith("g(x)") + "export function g(x: number): number { return x; }\n";
    expect(classifications(src).classified).toEqual([
      ["Error", "'f' could not be modeled: no model registered for 'g'"],
    ]);
  });

  test("a call to an earlier mappable declaration emits", () => {
    const src =
      "export function g(x: number): number { return x; }\n" + fnWith("g(x)");
    expect(classifications(src)).toEqual({ classified: [], obligations: 1 });
  });

  test("an arity mismatch fails the caller", () => {
    const src =
      "export function g(x: number): number { return x; }\n" +
      fnWith("g(x, x)");
    expect(classifications(src).classified).toEqual([
      ["Error", "'f' could not be modeled: 'g' expects 1 argument(s), got 2"],
    ]);
  });

  test("a construct-blocked callee records its construct inside its own body", () => {
    const src =
      "export function g(x: number): number { return x.y; }\n" + fnWith("g(x)");
    expect(residualConstructs(src)).toEqual([
      "unmapped TypeScript construct 'PropertyAccessExpression' at 1:47",
    ]);
  });

  // A type mismatch carries no construct, so it is the vehicle for a
  // callee that failed on the engine's side rather than the input's.
  test("an engine-failed callee stays the engine's Error", () => {
    const src =
      "export function g(x: number): number { return x < 7; }\n" +
      fnWith("g(x)");
    expect(classifications(src).classified).toEqual([
      [
        "Error",
        "'f' could not be modeled: 'g' has no model: operator '<' yields a " +
          "boolean, not a number",
      ],
    ]);
  });

  // A construct-less failure has nothing to travel, so the value-position
  // read reports the reason itself rather than the alias or travel wording.
  test("a value read of an engine-failed declaration reports its reason", () => {
    const src =
      "export function g(x: number): number { return x < 7; }\n" + fnWith("g");
    expect(classifications(src).classified).toEqual([
      [
        "Error",
        "'f' could not be modeled: 'g' has no model: operator '<' yields a " +
          "boolean, not a number",
      ],
    ]);
  });
});

describe("statement bodies (#148)", () => {
  const annotated = (decl: string) =>
    `/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n${decl}\n`;

  test("a branching, throwing, reassigning body maps statement for statement", () => {
    const src = annotated(
      [
        "export function f(x: number): number {",
        "  const bonus = 2;",
        "  if (x < 0) {",
        "    throw new RangeError(`bad: ${x}`);",
        "  } else if (x < 2) {",
        "    return x + bonus;",
        "  }",
        "  let rank = 0;",
        "  if (x < 4) {",
        "    rank = 1;",
        "  } else {",
        "    rank = 2;",
        "  }",
        "  return rank;",
        "}",
      ].join("\n"),
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      { kind: "const", name: "bonus", init: { kind: "num", lit: "2" } },
      {
        kind: "if",
        cond: {
          kind: "binop",
          op: "<",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "0" },
        },
        then: [{ kind: "throw", error: "RangeError" }],
        else: [
          {
            kind: "if",
            cond: {
              kind: "binop",
              op: "<",
              left: { kind: "id", name: "x" },
              right: { kind: "num", lit: "2" },
            },
            then: [
              {
                kind: "return",
                expr: {
                  kind: "binop",
                  op: "+",
                  left: { kind: "id", name: "x" },
                  right: { kind: "id", name: "bonus" },
                },
              },
            ],
          },
        ],
      },
      { kind: "let", name: "rank", init: { kind: "num", lit: "0" } },
      {
        kind: "if",
        cond: {
          kind: "binop",
          op: "<",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "4" },
        },
        then: [
          { kind: "assign", name: "rank", expr: { kind: "num", lit: "1" } },
        ],
        else: [
          { kind: "assign", name: "rank", expr: { kind: "num", lit: "2" } },
        ],
      },
      { kind: "return", expr: { kind: "id", name: "rank" } },
    ]);
  });

  test("a parameter reassignment maps like any mutable local", () => {
    const src = annotated(
      "export function f(x: number): number { if (x < 1) { x = 1; } return x; }",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "if",
        cond: {
          kind: "binop",
          op: "<",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "1" },
        },
        then: [{ kind: "assign", name: "x", expr: { kind: "num", lit: "1" } }],
      },
      { kind: "return", expr: { kind: "id", name: "x" } },
    ]);
  });

  test("a tail behind a branch whose arms both leave never reaches the artifact", () => {
    const src = annotated(
      "export function f(x: number): number { if (x < 0) { return 0; } else { return 1; } return q; }",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toHaveLength(1);
  });

  test("an empty arm keeps its statement, an empty else is dropped", () => {
    const src = annotated(
      "export function f(x: number): number { if (x < 0) {} else {} return x; }",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual({
      kind: "if",
      cond: {
        kind: "binop",
        op: "<",
        left: { kind: "id", name: "x" },
        right: { kind: "num", lit: "0" },
      },
      then: [],
    });
  });

  test.each([
    [
      "a redeclaration of a parameter",
      "export function f(x: number): number { const x = 1; return x; }",
      "VariableStatement",
    ],
    [
      "an arm's redeclaration of an enclosing binding",
      "export function f(x: number): number { const y = 1; if (x > 0) { const y = 2; return y; } return y; }",
      "VariableStatement",
    ],
    [
      "an uninitialized let",
      "export function f(x: number): number { let y: number; y = x; return y; }",
      "VariableStatement",
    ],
    [
      "a var declaration",
      "export function f(x: number): number { var y = 1; return y; }",
      "VariableStatement",
    ],
    [
      "a throw of a non-constructor value",
      "export function f(x: number): number { throw x; }",
      "ThrowStatement",
    ],
    [
      "a bare nested block",
      "export function f(x: number): number { { return x; } }",
      "Block",
    ],
    [
      "a using declaration, despite sharing the Const flag",
      "export function f(x: number): number { await using y = x; return x; }",
      "VariableStatement",
    ],
    [
      "a const statement with no declarators",
      "export function f(x: number): number { const; return x; }",
      "VariableStatement",
    ],
    [
      "a destructuring declarator",
      "export function f(x: number): number { const { y } = x; return x; }",
      "VariableStatement",
    ],
    [
      "a non-number declarator annotation",
      'export function f(x: number): number { const y: string = "a"; return x; }',
      "VariableStatement",
    ],
    [
      "a throw of a non-identifier constructor",
      "export function f(x: number): number { throw new Foo.Bar(); }",
      "ThrowStatement",
    ],
  ])(
    "%s classifies Inappropriate on its construct",
    (_label, decl, construct) => {
      expect(classifications(annotated(decl)).classified).toEqual([
        [
          "Inappropriate",
          expect.stringMatching(
            new RegExp(
              `^'f' could not be modeled: unmapped TypeScript construct '${construct}' at 2:\\d+$`,
            ),
          ),
        ],
      ]);
    },
  );

  test.each([
    [
      "a compound assignment",
      "export function f(x: number): number { x += 1; return x; }",
    ],
    [
      "an assignment to a const",
      "export function f(x: number): number { const y = 1; y = 2; return y; }",
    ],
    [
      "an assignment to a property",
      "export function f(x: number): number { x.y = 1; return x; }",
    ],
  ])("%s classifies Inappropriate naming the assignment", (_label, decl) => {
    expect(classifications(annotated(decl)).classified).toEqual([
      [
        "Inappropriate",
        expect.stringMatching(
          /^'f' could not be modeled: an assignment at 2:\d+ is inside an expression the model cannot follow$/,
        ),
      ],
    ]);
  });

  test.each([
    [
      "a truthiness condition",
      "export function f(x: number): number { if (x) { return 1; } return 0; }",
      "Identifier",
    ],
    [
      "a construct inside a declarator's initializer",
      "export function f(x: number): number { const y = x.q; return y; }",
      "PropertyAccessExpression",
    ],
    [
      "a construct inside a reassignment's value",
      "export function f(x: number): number { let y = 1; y = x.q; return y; }",
      "PropertyAccessExpression",
    ],
  ])("%s records its construct at the site", (_label, decl, construct) => {
    expect(residualConstructs(annotated(decl))).toEqual([
      expect.stringMatching(
        new RegExp(`^unmapped TypeScript construct '${construct}' at 2:\\d+$`),
      ),
    ]);
  });

  test("a call statement to a degraded callee records its construct at the site", () => {
    const src =
      "declare function log(n: number): void;\n" +
      annotated("export function f(x: number): number { log(x); return x; }");
    expect(residualConstructs(src)).toEqual([
      "'log' could not be modeled: unmapped TypeScript construct " +
        "'DeclareKeyword' at 1:1",
    ]);
  });

  test("a number-annotated declarator maps like a bare one", () => {
    const src = annotated(
      "export function f(x: number): number { const y: number = 2 * x; return y; }",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "const",
        name: "y",
        init: {
          kind: "binop",
          op: "*",
          left: { kind: "num", lit: "2" },
          right: { kind: "id", name: "x" },
        },
      },
      { kind: "return", expr: { kind: "id", name: "y" } },
    ]);
  });

  test("an else arm that leaves keeps the tail after the branch", () => {
    const src = annotated(
      "export function f(x: number): number { let y = x; if (x < 0) { y = 1; } else { return 0; } return y; }",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      { kind: "let", name: "y", init: { kind: "id", name: "x" } },
      {
        kind: "if",
        cond: {
          kind: "binop",
          op: "<",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "0" },
        },
        then: [{ kind: "assign", name: "y", expr: { kind: "num", lit: "1" } }],
        else: [{ kind: "return", expr: { kind: "num", lit: "0" } }],
      },
      { kind: "return", expr: { kind: "id", name: "y" } },
    ]);
  });

  test("an arm's own binding dies with the arm", () => {
    const src = annotated(
      "export function f(x: number): number { if (x < 0) { const y = 1; x = y; } return y; }",
    );
    expect(classifications(src).classified).toEqual([
      ["Error", "'f' could not be modeled: unbound identifier 'y'"],
    ]);
  });

  test("a body that can fall past a one-armed branch degrades", () => {
    const src = annotated(
      "export function f(x: number): number { if (x < 0) { return 0; } }",
    );
    expect(classifications(src).classified).toEqual([
      ["Error", "'f' could not be modeled: the body must return on every path"],
    ]);
  });
});

describe("formula classification", () => {
  test("** in a formula is Inappropriate with the bare reason", () => {
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { f(x) ** 2 >= 0 }"),
      ),
    ).toEqual({
      classified: [["Inappropriate", "'**' is not supported"]],
      obligations: 0,
    });
  });

  test("** in a guard is Inappropriate with the bare reason", () => {
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { x ** 2 >= 0 -> f(x) >= 0 }"),
      ),
    ).toEqual({
      classified: [["Inappropriate", "'**' is not supported"]],
      obligations: 0,
    });
  });

  test("a number-valued atom under ∨ refuses at the operator", () => {
    // Island typing refuses this atom before the emitter in the CLI; here the
    // emitter's own operand pre-scan answers.
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { f(x) ∨ x === 0 -> f(x) >= 0 }"),
      ),
    ).toEqual({
      classified: [
        [
          "Inappropriate",
          "'||' models boolean operands only; the left operand is not a " +
            "boolean (CallExpression at 1:3)",
        ],
      ],
      obligations: 0,
    });
  });

  // Guards precede the conclusion in the scan, so the two refusals must be
  // distinguishable: the reported one is the guard's.
  test("a refused guard is reported before a refused conclusion", () => {
    expect(
      classifications(
        formulaWith(
          "forall (x: int ∈ [0, 5)) { (await f(x)) >= 0 -> foo.bar(x) }",
        ),
      ).classified,
    ).toEqual([
      [
        "Inappropriate",
        "unmapped TypeScript construct 'AwaitExpression' at 1:3",
      ],
    ]);
  });

  test("an operator with no model refuses the property as outside the model", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { (x & 7) >= 0 }"))
        .classified,
    ).toEqual([["Inappropriate", "'&' is not supported"]]);
  });

  test("an unmapped construct is Inappropriate at its atom coordinates", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { foo.bar(x, x) }"))
        .classified,
    ).toEqual([
      [
        "Inappropriate",
        "unmapped TypeScript construct 'CallExpression' at 1:2",
      ],
    ]);
  });

  test("an await inside an equation side is Inappropriate", () => {
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { (await f(x)) ≡ x }"),
      ).classified,
    ).toEqual([
      [
        "Inappropriate",
        "'Object.is' admits numbers, booleans, union values, 'undefined', " +
          "and 'null'; argument 1 is not one (AwaitExpression at 1:13)",
      ],
    ]);
  });

  // Behind the CLI these never fire: island typing refuses an ill-typed
  // atom before emission. They pin the walk's own check, the engine-bug
  // signal, which emitModule still reaches when called directly.
  test("an unbound identifier is the walk's invariant Error", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { f(x) ≡ q }"))
        .classified,
    ).toEqual([
      ["Error", "property elaboration failed: unbound identifier 'q'"],
    ]);
  });

  test("a number-valued conclusion call is the walk's invariant Error", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { f(x) }"))
        .classified,
    ).toEqual([
      [
        "Error",
        "property elaboration failed: a call to 'f' yields a number, not a boolean",
      ],
    ]);
  });

  test("a numeric conclusion atom is the walk's invariant Error", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { x + 1 }"))
        .classified,
    ).toEqual([
      [
        "Error",
        "property elaboration failed: operator '+' yields a number, not a boolean",
      ],
    ]);
  });

  test.each([
    ["a numeric literal", "5", "a numeric literal cannot be a boolean"],
    ["an identifier", "x", "identifier 'x' is a number, not a boolean"],
    ["a unary minus", "-x", "operator '-' yields a number, not a boolean"],
  ])(
    "%s as the whole conclusion is the walk's invariant Error",
    (_label, atom, message) => {
      expect(
        classifications(formulaWith(`forall (x: int ∈ [0, 5)) { ${atom} }`))
          .classified,
      ).toEqual([["Error", `property elaboration failed: ${message}`]]);
    },
  );

  test("a comparison as an equation side lowers over the tagged domain (#209)", () => {
    const { emission, classified } = emitModule(
      formulaWith("forall (x: int ∈ [0, 5)) { (x < 1) ≡ x }"),
      "t.ts",
    );
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toEqual({
      kind: "istrue",
      expr: {
        kind: "jsval-eq",
        semantics: "same-value",
        left: {
          kind: "inject",
          tag: "boolean",
          expr: {
            kind: "binop",
            op: "<",
            left: { kind: "id", name: "x" },
            right: { kind: "num", lit: "1" },
          },
        },
        right: {
          kind: "inject",
          tag: "number",
          expr: { kind: "id", name: "x" },
        },
      },
    });
  });
});

describe("class-valued binders lower to a binder IR", () => {
  const BOX = "export class Box { constructor(readonly size: number) {} }\n";
  const POINT = [
    "export class Point {",
    "  readonly x: number;",
    "  readonly y: number;",
    "  constructor(x: number, y: number) { this.x = x; this.y = y; }",
    "  /** @ensures{nn} forall (p: Point) (q: Point) { p.gap(q) >= 0 } */",
    "  gap(q: Point): number { return 0; }",
    "}",
    "",
  ].join("\n");

  test("a class binder lowers to a class binder IR", () => {
    const { emission } = emitModule(POINT, "t.ts");
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    const xy = [
      { name: "x", kind: "number" },
      { name: "y", kind: "number" },
    ];
    expect(payload.binders).toEqual([
      { name: "p", kind: "class", className: "Point", ctorParams: xy },
      { name: "q", kind: "class", className: "Point", ctorParams: xy },
    ]);
  });

  test("a method call on a class binder resolves to the class's method", () => {
    const { emission } = emitModule(POINT, "t.ts");
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    assert(payload.conclusion.kind === "istrue");
    const expr = payload.conclusion.expr;
    assert(expr.kind === "binop");
    expect(expr.left).toEqual({
      kind: "method-call",
      className: "Point",
      name: "gap",
      object: { kind: "id", name: "p" },
      args: [{ kind: "id", name: "q" }],
    });
  });

  test("a class binder carries its constructor's parameter spellings", () => {
    const src = [
      "export class Span {",
      "  readonly lo: number;",
      "  readonly hi: number;",
      "  constructor(first: number, second: number) {",
      "    this.lo = first;",
      "    this.hi = second;",
      "  }",
      "}",
      "/** @ensures{p} forall (s: Span) { scale(1) >= 0 } */",
      "export function scale(x: number): number { return x; }",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "t.ts");
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.binders).toEqual([
      {
        name: "s",
        kind: "class",
        className: "Span",
        ctorParams: [
          { name: "first", kind: "number" },
          { name: "second", kind: "number" },
        ],
      },
    ]);
  });

  test("a binder naming a degraded class travels the class's reason", () => {
    const src =
      BOX +
      "/** @ensures{p} forall (b: Box) { scale(1) >= 0 } */\n" +
      "export function scale(x: number): number { return x; }\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "class-valued binder 'Box' names a class outside the model: " +
          "unmapped TypeScript construct 'ReadonlyKeyword' at 1:32",
      ],
    ]);
    expect(emission.obligations).toEqual([]);
    expect(emission.declarations.map((d) => declName(d))).toEqual(["scale"]);
  });

  test("a binder whose class takes a class-typed parameter lowers recursively", () => {
    const src = [
      "export class Inner {",
      "  readonly v: number;",
      "  constructor(v: number) { this.v = v; }",
      "}",
      "export class Outer { constructor(i: Inner) {} }",
      "/** @ensures{p} forall (o: Outer) { scale(1) >= 0 } */",
      "export function scale(x: number): number { return x; }",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "t.ts");
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.binders).toEqual([
      {
        name: "o",
        kind: "class",
        className: "Outer",
        ctorParams: [
          {
            name: "i",
            kind: "class",
            className: "Inner",
            ctorParams: [{ name: "v", kind: "number" }],
          },
        ],
      },
    ]);
  });

  test("a mixed constructor signature keeps its parameters in order", () => {
    const src = [
      "export class Inner {",
      "  readonly v: number;",
      "  constructor(v: number) { this.v = v; }",
      "}",
      "export class Outer { constructor(i: Inner, k: number) {} }",
      "/** @ensures{p} forall (o: Outer) { scale(1) >= 0 } */",
      "export function scale(x: number): number { return x; }",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "t.ts");
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    assert(payload.binders[0]!.kind === "class");
    expect(payload.binders[0]!.ctorParams).toEqual([
      {
        name: "i",
        kind: "class",
        className: "Inner",
        ctorParams: [{ name: "v", kind: "number" }],
      },
      { name: "k", kind: "number" },
    ]);
  });

  test("a three-class chain lowers all the way down", () => {
    const src = [
      "export class A { constructor(a: number) {} }",
      "export class B { constructor(a: A) {} }",
      "export class C { constructor(b: B) {} }",
      "/** @ensures{p} forall (c: C) { scale(1) >= 0 } */",
      "export function scale(x: number): number { return x; }",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "t.ts");
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    assert(payload.binders[0]!.kind === "class");
    expect(payload.binders[0]!.ctorParams).toEqual([
      {
        name: "b",
        kind: "class",
        className: "B",
        ctorParams: [
          {
            name: "a",
            kind: "class",
            className: "A",
            ctorParams: [{ name: "a", kind: "number" }],
          },
        ],
      },
    ]);
  });

  test("a binder naming nothing the module declares refuses", () => {
    const src =
      "/** @ensures{p} forall (b: Nope) { scale(1) >= 0 } */\n" +
      "export function scale(x: number): number { return x; }\n";
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        "class-valued binder 'Nope' names a class outside the model: " +
          "no model registered for 'Nope'",
      ],
    ]);
  });

  test("the binder refusal wins over other blockers in the same property", () => {
    const src =
      BOX +
      "/** @ensures{p} forall (b: Box) (s: string) { scale(1) >= 0 } */\n" +
      "export function scale(x: number): number { return x; }\n";
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        "class-valued binder 'Box' names a class outside the model: " +
          "unmapped TypeScript construct 'ReadonlyKeyword' at 1:32",
      ],
    ]);
  });

  test("a defaulted constructor parameter models, quantified at its declared type", () => {
    const src = [
      "export class P {",
      "  readonly x: number;",
      "  readonly y: number;",
      "  constructor(x: number, y: number = 0) {",
      "    this.x = x;",
      "    this.y = y;",
      "  }",
      "  /** @ensures{nn} forall (p: P) { p.span() >= 0 } */",
      "  span(): number { return this.x * this.x + this.y * this.y; }",
      "}",
      "",
    ].join("\n");
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.binders).toEqual([
      {
        name: "p",
        kind: "class",
        className: "P",
        ctorParams: [
          { name: "x", kind: "number" },
          { name: "y", kind: "number", defaulted: true },
        ],
      },
    ]);
  });

  test("a full-arity formula call to a defaulted constructor models", () => {
    const src = [
      "export class P {",
      "  readonly x: number;",
      "  readonly y: number;",
      "  constructor(x: number, y: number = 0) {",
      "    this.x = x;",
      "    this.y = y;",
      "  }",
      "  /** @ensures{p} forall (a: int ∈ [0, 5)) { new P(a, a).span() >= 0 } */",
      "  span(): number { return this.x * this.x + this.y * this.y; }",
      "}",
      "",
    ].join("\n");
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("a defaulted method parameter models", () => {
    const src = [
      "export class C {",
      "  readonly x: number;",
      "  constructor(x: number) { this.x = x; }",
      "  /** @ensures{p} forall (a: int ∈ [0, 5)) { new C(a).plus(a) >= 0 } */",
      "  plus(k: number = 1): number { return this.x + k; }",
      "}",
      "",
    ].join("\n");
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("a defaulted parameter with no type annotation still degrades the class", () => {
    const src = [
      "export class C { constructor(y = 0) {} }",
      "/** @ensures{p} forall (c: C) { scale(1) >= 0 } */",
      "export function scale(x: number): number { return x; }",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "t.ts");
    expect(classified.map((c) => c.szs)).toEqual(["Inappropriate"]);
    expect(classified[0]!.reason).toMatch(
      /class-valued binder 'C' names a class outside the model: unmapped TypeScript construct 'Parameter' at 1:\d+/,
    );
  });
});

describe("non-function declarations degrade before emission", () => {
  test("a caller of a top-level const records VariableStatement at the site", () => {
    const src = [
      "const double = (x: number): number => x * 2;",
      "/** @ensures{pos} forall (n: int ∈ [0, 4)) { applyDouble(n) >= 0 } */",
      "export function applyDouble(n: number): number {",
      "  return double(n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "consts.ts")).toEqual([
      "'double' could not be modeled: " +
        "unmapped TypeScript construct 'VariableStatement' at 1:7",
    ]);
  });

  test("a formula mentioning a top-level const classifies Inappropriate", () => {
    const src = [
      "const scale = (x: number): number => x * 2;",
      "/** @ensures{eq} forall (n: int ∈ [0, 4)) { keep(n) === scale(n) } */",
      "export function keep(n: number): number {",
      "  return n;",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "consts.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toBe(
      "'scale' could not be modeled: " +
        "unmapped TypeScript construct 'VariableStatement' at 1:7",
    );
  });

  test("destructuring declarators register every bound name", () => {
    const src = [
      "const { lo, hi } = { lo: 1, hi: 2 };",
      "/** @ensures{pos} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return lo(n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "destructure.ts")).toEqual([
      expect.stringContaining("'VariableStatement' at 1:9"),
    ]);
  });

  test("import bindings register as failed with ImportDeclaration", () => {
    const src = [
      "import { g } from 'somepkg';",
      "/** @ensures{pos} forall (n: int ∈ [0, 4)) { h(n) >= 0 } */",
      "export function h(n: number): number {",
      "  return g(n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "imports.ts")).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'ImportDeclaration' at 1:10",
      ),
    ]);
  });

  test("default and namespace import bindings register as failed", () => {
    const src = [
      "import dflt, * as ns from 'somepkg';",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { viaDefault(n) >= 0 } */",
      "export function viaDefault(n: number): number {",
      "  return dflt(n);",
      "}",
      "/** @ensures{q} forall (n: int ∈ [0, 4)) { viaNamespace(n) >= 0 } */",
      "export function viaNamespace(n: number): number {",
      "  return ns(n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "imports.ts")).toEqual([
      expect.stringContaining("'ImportDeclaration' at 1:8"),
      expect.stringContaining("'ImportDeclaration' at 1:19"),
    ]);
  });

  test("a side-effect import binds nothing; a lone default still registers", () => {
    const src = [
      "import 'polyfill';",
      "import only from 'somepkg';",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { viaOnly(n) >= 0 } */",
      "export function viaOnly(n: number): number {",
      "  return only(n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "imports.ts")).toEqual([
      expect.stringContaining("'ImportDeclaration' at 2:8"),
    ]);
  });
});

describe("unsupported ranges classify NotTried before emission", () => {
  const HUGE =
    "/** @ensures{nonneg} forall (x: int ∈ [0, 1000000000000000000000000000000]) { keep(x) >= 0 } */\n" +
    "export function keep(x: number): number {\n  return x;\n}\n";

  test("a clamped endpoint classifies NotTried, naming the endpoint", () => {
    const { classified, emission } = emitModule(HUGE, "huge.ts");
    expect(emission.obligations).toEqual([]);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
      }),
    ]);
  });

  test("a clamp that is not the sole blocker degrades to bare", () => {
    // The biconditional keeps the body unstructurable, so the clamp never wins.
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 1000000000000000000000000000000]) { keep(x) >= 0 ↔ keep(x) <= x } */\n" +
      "export function keep(x: number): number {\n  return x;\n}\n";
    const { classified, emission } = emitModule(src, "huge-bare.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toEqual({ kind: "bare" });
  });

  test("a clamp under a connective body is the sole blocker and reports unsupported-range", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 1000000000000000000000000000000]) { keep(x) >= 0 ∨ keep(x) <= x } */\n" +
      "export function keep(x: number): number {\n  return x;\n}\n";
    const { classified } = emitModule(src, "huge-or.ts");
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
      }),
    ]);
  });

  test("an interval the clamp empties is unsupported-range whatever the body", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [1000000000000000000000000000000, 10000000000000000000000000000000]) { keep(x) >= 0 && keep(x) <= x } */\n" +
      "export function keep(x: number): number {\n  return x;\n}\n";
    const { classified } = emitModule(src, "empty.ts");
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "NotTried",
        kind: "unsupported-range",
        reason:
          "endpoints 1000000000000000000000000000000 and 10000000000000000000000000000000 exceed the safe integer range (±9007199254740991)",
      }),
    ]);
  });
});

describe("Object.is models as SameValue", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts"; // any resolvable path; no imports are followed

  test("a branch condition walks to a same-value node", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { canon(n) === 0 } */",
      "export function canon(x: number): number {",
      "  if (Object.is(x, -0)) {",
      "    return 0;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "canon",
        body: [
          {
            kind: "if",
            cond: {
              kind: "same-value",
              left: { kind: "id", name: "x" },
              right: { kind: "num", lit: "-0" },
            },
            then: [{ kind: "return", expr: { kind: "num", lit: "0" } }],
          },
          { kind: "return", expr: { kind: "num", lit: "0" } },
        ],
      }),
    ]);
  });

  test("a negated identifier argument is numeric-shaped and walks", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { canon(n) === 0 } */",
      "export function canon(x: number): number {",
      "  if (Object.is(-x, 0)) {",
      "    return 0;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual(
      expect.objectContaining({
        cond: {
          kind: "same-value",
          left: { kind: "unop", op: "-", operand: { kind: "id", name: "x" } },
          right: { kind: "num", lit: "0" },
        },
      }),
    );
  });

  test("a non-numeric argument refuses the declaration, never a site", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { pick(x) === 1 } */",
      "export function pick(x: number): number {",
      '  if (Object.is(x, "zero")) {',
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    const { classified, emission } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "'Object.is' admits numbers, booleans, union values",
        ),
      }),
    ]);
    expect(emission.declarations).toEqual([]);
  });

  test("a bool-valued argument injects at the boolean tag (#209)", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { pick(x) === 1 } */",
      "export function pick(x: number): number {",
      "  if (Object.is(x < 1, 0)) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual(
      expect.objectContaining({
        cond: {
          kind: "jsval-eq",
          semantics: "same-value",
          left: {
            kind: "inject",
            tag: "boolean",
            expr: {
              kind: "binop",
              op: "<",
              left: { kind: "id", name: "x" },
              right: { kind: "num", lit: "1" },
            },
          },
          right: {
            kind: "inject",
            tag: "number",
            expr: { kind: "num", lit: "0" },
          },
        },
      }),
    );
  });

  test("the undefined atom against a plain number injects without a union (#209)", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { pick(x) === 1 } */",
      "export function pick(x: number): number {",
      "  if (Object.is(x, undefined)) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual(
      expect.objectContaining({
        cond: {
          kind: "jsval-eq",
          semantics: "same-value",
          left: {
            kind: "inject",
            tag: "number",
            expr: { kind: "id", name: "x" },
          },
          right: { kind: "inject", tag: "undefined" },
        },
      }),
    );
  });

  test("Object.is in a num position is a type mismatch, the engine's Error", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { toBit(x) === 1 } */",
      "export function toBit(x: number): number {",
      "  return Object.is(x, 0);",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Error",
        reason: expect.stringContaining(
          "a call to 'Object.is' yields a boolean, not a number",
        ),
      }),
    ]);
  });

  test("a failed callee inside an Object.is argument still travels", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { pick(x) === 1 } */",
      "export function broken(x: number): number {",
      "  while (true) {}",
      "}",
      "export function pick(x: number): number {",
      "  if (Object.is(broken(x), 0)) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("'broken' could not be modeled"),
      }),
    ]);
  });

  test("a wrong-arity Object.is stays the unmapped call it was", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { pick(x) === 1 } */",
      "export function pick(x: number): number {",
      "  if (Object.is(x)) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct"),
    ]);
  });
});

describe("equation guards", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts";
  const src = (formula: string) =>
    [
      `/** @ensures{p} ${formula} */`,
      "export function pick(x: number): number {",
      "  return x;",
      "}",
    ].join("\n");

  test("an ≡ guard walks to a same-value hypothesis", () => {
    const { emission } = emitModule(
      src("forall (n: int ∈ [0, 2)) { n ≡ 1 -> pick(n) === 1 }"),
      FILE,
    );
    expectValidEmission(emission);
    expect(emission.obligations).toEqual([
      expect.objectContaining({
        payload: expect.objectContaining({
          kind: "structured",
          guards: [
            {
              kind: "same-value",
              left: { kind: "id", name: "n" },
              right: { kind: "num", lit: "1" },
            },
          ],
        }),
      }),
    ]);
  });

  test("a ≢ guard walks to a negated same-value hypothesis", () => {
    const { emission } = emitModule(
      src("forall (n: int ∈ [0, 2)) { n ≢ 1 -> pick(n) === 1 }"),
      FILE,
    );
    expectValidEmission(emission);
    expect(emission.obligations).toEqual([
      expect.objectContaining({
        payload: expect.objectContaining({
          kind: "structured",
          guards: [
            {
              kind: "unop",
              op: "!",
              operand: {
                kind: "same-value",
                left: { kind: "id", name: "n" },
                right: { kind: "num", lit: "1" },
              },
            },
          ],
        }),
      }),
    ]);
  });

  test("a ∨ guard walks to one || hypothesis", () => {
    const { emission } = emitModule(
      src("forall (n: int ∈ [0, 4)) { n === 0 ∨ n === 1 -> pick(n) <= 1 }"),
      FILE,
    );
    expectValidEmission(emission);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.guards).toEqual([
      {
        kind: "binop",
        op: "||",
        left: {
          kind: "binop",
          op: "===",
          left: { kind: "id", name: "n" },
          right: { kind: "num", lit: "0" },
        },
        right: {
          kind: "binop",
          op: "===",
          left: { kind: "id", name: "n" },
          right: { kind: "num", lit: "1" },
        },
      },
    ]);
    expect(payload.conclusion).toEqual({
      kind: "istrue",
      expr: {
        kind: "binop",
        op: "<=",
        left: {
          kind: "call",
          callee: "pick",
          args: [{ kind: "id", name: "n" }],
        },
        right: { kind: "num", lit: "1" },
      },
    });
  });

  test("an ∧ conclusion is one && island, never an equation", () => {
    const { emission } = emitModule(
      src("forall (n: int ∈ [0, 4)) { pick(n) >= 0 ∧ pick(n) ≡ n }"),
      FILE,
    );
    expectValidEmission(emission);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.guards).toBeUndefined();
    expect(payload.conclusion).toEqual({
      kind: "istrue",
      expr: {
        kind: "binop",
        op: "&&",
        left: {
          kind: "binop",
          op: ">=",
          left: {
            kind: "call",
            callee: "pick",
            args: [{ kind: "id", name: "n" }],
          },
          right: { kind: "num", lit: "0" },
        },
        right: {
          kind: "same-value",
          left: {
            kind: "call",
            callee: "pick",
            args: [{ kind: "id", name: "n" }],
          },
          right: { kind: "id", name: "n" },
        },
      },
    });
  });

  test("a ¬ conclusion is a ! island", () => {
    const { emission } = emitModule(
      src("forall (n: int ∈ [0, 4)) { ¬(pick(n) > 100) }"),
      FILE,
    );
    expectValidEmission(emission);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toEqual({
      kind: "istrue",
      expr: {
        kind: "unop",
        op: "!",
        operand: {
          kind: "binop",
          op: ">",
          left: {
            kind: "call",
            callee: "pick",
            args: [{ kind: "id", name: "n" }],
          },
          right: { kind: "num", lit: "100" },
        },
      },
    });
  });

  test("¬(A ≡ B) and A ≢ B walk to the same guard", () => {
    const negated = emitModule(
      src("forall (n: int ∈ [0, 2)) { ¬(n ≡ 1) -> pick(n) === 1 }"),
      FILE,
    ).emission;
    const glyph = emitModule(
      src("forall (n: int ∈ [0, 2)) { n ≢ 1 -> pick(n) === 1 }"),
      FILE,
    ).emission;
    expectValidEmission(negated);
    assert(negated.obligations[0]!.payload.kind === "structured");
    expect(negated.obligations[0]!.payload).toEqual(
      glyph.obligations[0]!.payload,
    );
  });

  test("a top-level equation conclusion still maps to eq, not same-value", () => {
    const { emission } = emitModule(
      src("forall (n: int ∈ [0, 2)) { pick(n) ≡ n }"),
      FILE,
    );
    expect(emission.obligations).toEqual([
      expect.objectContaining({
        payload: expect.objectContaining({
          conclusion: expect.objectContaining({ kind: "eq" }),
        }),
      }),
    ]);
  });
});

describe("NaN and Infinity resolve as expression atoms", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts"; // any resolvable path; no imports are followed

  test("NaN in a body walks to a num atom", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { addNaN(n) >= 0 } */",
      "export function addNaN(x: number): number {",
      "  return x + NaN;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "binop",
          op: "+",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "NaN" },
        },
      },
    ]);
  });

  test("NaN in a formula atom walks to a num atom", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { Object.is(addNaN(n), NaN) } */",
      "export function addNaN(x: number): number {",
      "  return x + NaN;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual(
      expect.objectContaining({
        conclusion: expect.objectContaining({
          kind: "eq",
          right: { kind: "num", lit: "NaN" },
        }),
      }),
    );
  });

  test("-Infinity composes as unary minus over the Infinity atom", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { floor(n) >= -Infinity } */",
      "export function floor(x: number): number {",
      "  return -Infinity;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "unop",
          op: "-",
          operand: { kind: "num", lit: "Infinity" },
        },
      },
    ]);
  });

  test("Infinity in a branch comparison walks to a num atom", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { clampInf(n) === n } */",
      "export function clampInf(x: number): number {",
      "  if (x === Infinity) {",
      "    return 0;",
      "  }",
      "  return x;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual(
      expect.objectContaining({
        cond: {
          kind: "binop",
          op: "===",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "Infinity" },
        },
      }),
    );
  });

  test("a parameter spelled NaN shadows the global", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { ident(n) === n } */",
      "export function ident(NaN: number): number {",
      "  return NaN;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      { kind: "return", expr: { kind: "id", name: "NaN" } },
    ]);
  });

  test("a local spelled Infinity shadows the global", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { one(n) === 1 } */",
      "export function one(x: number): number {",
      "  const Infinity = 1;",
      "  return Infinity;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[1]).toEqual({
      kind: "return",
      expr: { kind: "id", name: "Infinity" },
    });
  });

  test("a module-level binding wins over the global: the read names it, not the atom", () => {
    const src = [
      "const NaN = 1;",
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { probe(n) === 1 } */",
      "export function probe(x: number): number {",
      "  return NaN;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[1]!)[0]).toEqual({
      kind: "return",
      expr: { kind: "const-read", name: "NaN" },
    });
  });

  test("a module-level binding of the spelling that stays unmodeled degrades the read", () => {
    const src = [
      "const NaN = somewhere();",
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { probe(n) === 1 } */",
      "export function probe(x: number): number {",
      "  return NaN;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'NaN' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement' at 1:7",
    ]);
  });

  test("a degraded import of the spelling also wins over the global", () => {
    const src = [
      'import { NaN } from "./missing.js";',
      "/** @ensures{p} forall (n: int ∈ [0, 2)) { probe(n) === 1 } */",
      "export function probe(x: number): number {",
      "  return NaN;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'NaN' could not be modeled: unmapped TypeScript construct " +
        "'ImportDeclaration' at 1:10",
    ]);
  });

  test("a NaN conclusion atom is a type mismatch, not an unbound name", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { NaN }"))
        .classified,
    ).toEqual([
      [
        "Error",
        "property elaboration failed: identifier 'NaN' is a number, not a boolean",
      ],
    ]);
  });
});

describe("Math.sqrt models as Float.sqrt", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts"; // any resolvable path; no imports are followed

  test("a returned Math.sqrt walks to a builtin node", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { root(n) >= 0 } */",
      "export function root(x: number): number {",
      "  return Math.sqrt(x);",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "root",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "sqrt",
              args: [{ kind: "id", name: "x" }],
            },
          },
        ],
      }),
    ]);
  });

  test("a formula atom calls Math.sqrt directly", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { Math.sqrt(n) >= 0 } */",
      "export function root(x: number): number {",
      "  return Math.sqrt(x);",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual(
      expect.objectContaining({
        conclusion: expect.objectContaining({
          expr: expect.objectContaining({
            left: {
              kind: "builtin",
              object: "Math",
              member: "sqrt",
              args: [{ kind: "id", name: "n" }],
            },
          }),
        }),
      }),
    );
  });

  test("Math.sqrt is numeric-shaped inside Object.is", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [1, 3)) { Object.is(negRoot(n), NaN) } */",
      "export function negRoot(x: number): number {",
      "  return Math.sqrt(-x);",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
  });

  test("a boolean position rejects the call as a number", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { Math.sqrt(n) } */",
      "export function root(x: number): number {",
      "  return Math.sqrt(x);",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Error",
        reason: expect.stringContaining(
          "a call to 'Math.sqrt' yields a number, not",
        ),
      }),
    ]);
  });

  test("Math.pow reports itself as unsupported", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { square(n) >= 0 } */",
      "export function square(x: number): number {",
      "  return Math.pow(x, 2);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'Math.pow' is not supported",
    ]);
  });

  test("an unlisted member in a formula atom reports itself from the walk", () => {
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { Math.log(x) >= 0 }"),
      ).classified,
    ).toEqual([["Inappropriate", "'Math.log' is not supported"]]);
  });

  test("a shadowed object is not a builtin, so its member stays a construct", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { lg(n, n) >= 0 } */",
      "export function lg(x: number, Math: number): number {",
      "  return Math.log(x);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("a wrong-arity Math.sqrt reports the count it takes", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { two(n) >= 0 } */",
      "export function two(x: number): number {",
      "  return Math.sqrt(x, 2);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'Math.sqrt' takes one argument",
    ]);
  });

  test("a no-argument Math.sqrt reports the same count", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { none(n) >= 0 } */",
      "export function none(x: number): number {",
      "  return Math.sqrt() + x;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("'Math.sqrt' takes one argument"),
    ]);
  });

  test("an unsupported operator inside the argument is still found", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { f(n) >= 0 } */",
      "export function f(x: number): number {",
      "  return Math.sqrt(x ** 2);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("**"),
    ]);
  });

  test.each([
    ["trunc", "Math.trunc(x)"],
    ["floor", "Math.floor(x)"],
    ["ceil", "Math.ceil(x)"],
    ["round", "Math.round(x)"],
    ["sign", "Math.sign(x)"],
    ["fround", "Math.fround(x)"],
  ])("Math.%s walks to a builtin node", (member, call) => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { r(n) >= 0 } */",
      "export function r(x: number): number {",
      `  return ${call};`,
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "r",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member,
              args: [{ kind: "id", name: "x" }],
            },
          },
        ],
      }),
    ]);
  });

  test("a formula atom calls Math.trunc directly", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { Math.trunc(n) >= 0 } */",
      "export function r(x: number): number {",
      "  return x;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual(
      expect.objectContaining({
        conclusion: expect.objectContaining({
          expr: expect.objectContaining({
            left: {
              kind: "builtin",
              object: "Math",
              member: "trunc",
              args: [{ kind: "id", name: "n" }],
            },
          }),
        }),
      }),
    );
  });
});

describe("builtin member calls model as Float primitives", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts"; // any resolvable path; no imports are followed

  test("a returned Math.abs walks to a builtin node", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [-5, 5)) { mag(n) >= 0 } */",
      "export function mag(x: number): number {",
      "  return Math.abs(x);",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "mag",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "abs",
              args: [{ kind: "id", name: "x" }],
            },
          },
        ],
      }),
    ]);
  });

  test("a boolean island conclusion admits Number.isInteger", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { Number.isInteger(bump(n)) } */",
      "export function bump(x: number): number {",
      "  return x + 1;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual(
      expect.objectContaining({
        conclusion: {
          kind: "istrue",
          expr: {
            kind: "builtin",
            object: "Number",
            member: "isInteger",
            args: [
              {
                kind: "call",
                callee: "bump",
                args: [{ kind: "id", name: "n" }],
              },
            ],
          },
        },
      }),
    );
  });

  test("Number.isSafeInteger works as a branch condition", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { flag(n) === 1 } */",
      "export function flag(x: number): number {",
      "  if (Number.isSafeInteger(x)) {",
      "    return 1;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "flag",
        body: [
          expect.objectContaining({
            kind: "if",
            cond: {
              kind: "builtin",
              object: "Number",
              member: "isSafeInteger",
              args: [{ kind: "id", name: "x" }],
            },
          }),
          expect.objectContaining({ kind: "return" }),
        ],
      }),
    ]);
  });

  test("a boolean island conclusion admits Number.isFinite", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { Number.isFinite(bump(n)) } */",
      "export function bump(x: number): number {",
      "  return x + 1;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual(
      expect.objectContaining({
        conclusion: {
          kind: "istrue",
          expr: {
            kind: "builtin",
            object: "Number",
            member: "isFinite",
            args: [
              {
                kind: "call",
                callee: "bump",
                args: [{ kind: "id", name: "n" }],
              },
            ],
          },
        },
      }),
    );
  });

  test("a Number.isFinite guard joins the guard chain", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { Number.isFinite(n) → half(n) <= n } */",
      "export function half(x: number): number {",
      "  return x / 2;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual(
      expect.objectContaining({
        guards: [
          {
            kind: "builtin",
            object: "Number",
            member: "isFinite",
            args: [{ kind: "id", name: "n" }],
          },
        ],
      }),
    );
  });

  test("a negated Number.isNaN walks under '!'", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { clean(n) >= 0 } */",
      "export function clean(x: number): number {",
      "  if (!Number.isNaN(x)) {",
      "    return x;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual(
      expect.objectContaining({
        cond: {
          kind: "unop",
          op: "!",
          operand: {
            kind: "builtin",
            object: "Number",
            member: "isNaN",
            args: [{ kind: "id", name: "x" }],
          },
        },
      }),
    );
  });

  test("Number.isNaN is boolean-shaped as a branch condition", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { clean(n) >= 0 } */",
      "export function clean(x: number): number {",
      "  if (Number.isNaN(x)) {",
      "    return 0;",
      "  }",
      "  return x;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual({
      kind: "if",
      cond: {
        kind: "builtin",
        object: "Number",
        member: "isNaN",
        args: [{ kind: "id", name: "x" }],
      },
      then: [{ kind: "return", expr: { kind: "num", lit: "0" } }],
    });
  });

  test("Number.isFinite composes with '&&' in a branch condition", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { pos(n) >= 0 } */",
      "export function pos(x: number): number {",
      "  if (Number.isFinite(x) && x > 0) {",
      "    return x;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual(
      expect.objectContaining({
        cond: {
          kind: "binop",
          op: "&&",
          left: {
            kind: "builtin",
            object: "Number",
            member: "isFinite",
            args: [{ kind: "id", name: "x" }],
          },
          right: expect.objectContaining({ op: ">" }),
        },
      }),
    );
  });

  test("a boolean position rejects Math.abs as a number", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { Math.abs(n) } */",
      "export function mag(x: number): number {",
      "  return Math.abs(x);",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Error",
        reason: expect.stringContaining(
          "a call to 'Math.abs' yields a number, not",
        ),
      }),
    ]);
  });

  test("a numeric position rejects Number.isFinite as a boolean", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { probe(n) >= 0 } */",
      "export function probe(x: number): number {",
      "  return Number.isFinite(x);",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Error",
        reason: expect.stringContaining(
          "a call to 'Number.isFinite' yields a boolean, not",
        ),
      }),
    ]);
  });

  test("a Number.isFinite argument makes a SameValue conclusion a boolean island (#209)", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { Object.is(Number.isFinite(n), n) } */",
      "export function probe(x: number): number {",
      "  return x;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toEqual({
      kind: "istrue",
      expr: {
        kind: "jsval-eq",
        semantics: "same-value",
        left: {
          kind: "inject",
          tag: "boolean",
          expr: {
            kind: "builtin",
            object: "Number",
            member: "isFinite",
            args: [{ kind: "id", name: "n" }],
          },
        },
        right: {
          kind: "inject",
          tag: "number",
          expr: { kind: "id", name: "n" },
        },
      },
    });
  });

  test("Object.is on a class-typed identifier refuses like the new spelling", () => {
    const src = [
      "export class Point {",
      "  readonly x: number;",
      "  constructor(x: number) {",
      "    this.x = x;",
      "  }",
      "}",
      "/** @ensures{p} forall (a: int ∈ [0, 10)) { Object.is(f(new Point(a)), 0) } */",
      "export function f(p: Point): number {",
      "  if (Object.is(p, 0)) {",
      "    return 1;",
      "  }",
      "  return 0;",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain(
      "'Object.is' admits numbers, booleans, union values, 'undefined', " +
        "and 'null'; argument 1 is not one (Identifier",
    );
  });

  test("Number.parseFloat reports itself as unsupported", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { conv(n) >= 0 } */",
      "export function conv(x: number): number {",
      "  return Number.parseFloat(x);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("'Number.parseFloat' is not supported"),
    ]);
  });

  test("a number-valued builtin as a condition is truthiness, not a member refusal", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { two(n) >= 0 } */",
      "export function two(x: number): number {",
      "  if (Math.abs(x)) {",
      "    return x;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("a wrong-arity Number.isFinite reports the count it takes", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { two(n) >= 0 } */",
      "export function two(x: number): number {",
      "  if (Number.isFinite(x, 2)) {",
      "    return x;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("'Number.isFinite' takes one argument"),
    ]);
  });

  test("a module-level binding of the namespace wins over the builtin", () => {
    const src = [
      "const Number = { isFinite: (v: number): boolean => v > 0 };",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { flag(n) === 1 } */",
      "export function flag(x: number): number {",
      "  if (Number.isFinite(x)) {",
      "    return 1;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("a degraded import of the namespace also wins over the builtin", () => {
    const src = [
      'import { Number } from "./missing.js";',
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { flag(n) === 1 } */",
      "export function flag(x: number): number {",
      "  if (Number.isFinite(x)) {",
      "    return 1;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("a module-level declaration of Math wins over the builtin", () => {
    const src = [
      "export function Math(): number {",
      "  return 0;",
      "}",
      "/** @ensures{p} forall (n: int ∈ [-5, 5)) { mag(n) >= 0 } */",
      "export function mag(x: number): number {",
      "  return Math.abs(x);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("a parameter named Math shadows the builtin in its own body", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { mag(n) >= 0 } */",
      "export function mag(Math: number): number {",
      "  return Math.abs(Math);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  // The pre-scan threads each decl's binding through the rest of its
  // list, so a local shadow is the scan's find, same as a parameter's:
  // `Inappropriate` at the construct. The builtin never lowers.
  test("a local named Number shadows the builtin from its declaration on", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { flag(n) === 1 } */",
      "export function flag(x: number): number {",
      "  const Number = x;",
      "  if (Number.isFinite(x)) {",
      "    return 1;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("a shadowed namespace in a formula atom is refused too", () => {
    const src = [
      "const Math = { abs: (v: number): number => v };",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { Math.abs(n) >= 0 } */",
      "export function probe(x: number): number {",
      "  return x;",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "unmapped TypeScript construct 'CallExpression'",
        ),
      }),
    ]);
  });

  test("Math.min carries both of a two-argument call's arguments", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { cap(n) <= 3 } */",
      "export function cap(x: number): number {",
      "  return Math.min(x, 3);",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "cap",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "min",
              args: [
                { kind: "id", name: "x" },
                { kind: "num", lit: "3" },
              ],
            },
          },
        ],
      }),
    ]);
  });

  test("Math.max carries three arguments", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { biggest(n) >= 0 } */",
      "export function biggest(x: number): number {",
      "  return Math.max(x, 0, 1);",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "biggest",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "max",
              args: [
                { kind: "id", name: "x" },
                { kind: "num", lit: "0" },
                { kind: "num", lit: "1" },
              ],
            },
          },
        ],
      }),
    ]);
  });

  test("a one-argument Math.min is still a builtin node", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { same(n) >= 0 } */",
      "export function same(x: number): number {",
      "  return Math.min(x);",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "same",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "min",
              args: [{ kind: "id", name: "x" }],
            },
          },
        ],
      }),
    ]);
  });

  test("a zero-argument Math.max is the identity, not a refusal", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { floorOf(n) <= 0 } */",
      "export function floorOf(x: number): number {",
      "  return Math.max() + 0 * x;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "floorOf",
        body: [
          {
            kind: "return",
            expr: expect.objectContaining({
              kind: "binop",
              left: {
                kind: "builtin",
                object: "Math",
                member: "max",
                args: [],
              },
            }),
          },
        ],
      }),
    ]);
  });

  test("a nested clamp folds both members", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 9)) { clamp(n) <= 5 } */",
      "export function clamp(x: number): number {",
      "  return Math.min(Math.max(x, 1), 5);",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "clamp",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "min",
              args: [
                {
                  kind: "builtin",
                  object: "Math",
                  member: "max",
                  args: [
                    { kind: "id", name: "x" },
                    { kind: "num", lit: "1" },
                  ],
                },
                { kind: "num", lit: "5" },
              ],
            },
          },
        ],
      }),
    ]);
  });

  test("a formula atom calls Math.min at three arguments", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 5)) { Math.min(n, n, n) >= 0 } */",
      "export function id(x: number): number {",
      "  return x;",
      "}",
    ].join("\n");
    const { emission } = emitModule(src, FILE);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toEqual(
      expect.objectContaining({
        conclusion: expect.objectContaining({
          expr: expect.objectContaining({
            left: {
              kind: "builtin",
              object: "Math",
              member: "min",
              args: [
                { kind: "id", name: "n" },
                { kind: "id", name: "n" },
                { kind: "id", name: "n" },
              ],
            },
          }),
        }),
      }),
    );
  });

  test("an unsupported operator inside a Math.abs argument is still found", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { f(n) >= 0 } */",
      "export function f(x: number): number {",
      "  return Math.abs(x ** 2);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("**"),
    ]);
  });
});

describe("logical operators on boolean operands", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts";

  test("|| over comparisons models in a branch condition", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (x === 0 || x === 1) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toMatchObject({
      kind: "if",
      cond: {
        kind: "binop",
        op: "||",
        left: { kind: "binop", op: "===" },
        right: { kind: "binop", op: "===" },
      },
    });
  });

  test("&& and ! compose in a branch condition", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (!(x === 0) && x < 3) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toMatchObject({
      kind: "if",
      cond: {
        kind: "binop",
        op: "&&",
        left: { kind: "unop", op: "!", operand: { kind: "binop", op: "===" } },
        right: { kind: "binop", op: "<" },
      },
    });
  });

  test("! over Object.is models in a branch condition", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (!Object.is(x, NaN)) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toMatchObject({
      kind: "if",
      cond: { kind: "unop", op: "!", operand: { kind: "same-value" } },
    });
  });

  test("a truthiness left operand records its site naming ||", () => {
    const src = [
      "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
      "export function pick(x: number): number {",
      "  if (x || 1) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'||' models boolean operands only; the left operand is not a " +
        "boolean (Identifier at 3:7)",
    ]);
  });

  test("a truthiness right operand records its site naming &&", () => {
    const src = [
      "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
      "export function pick(x: number): number {",
      "  if (x === 0 && 1) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'&&' models boolean operands only; the right operand is not a " +
        "boolean (NumericLiteral at 3:18)",
    ]);
  });

  test("a call to a shadowed callee is not a boolean-shaped operand", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) (cb: int in [0, 4)) { pick(x, cb) >= 0 } */",
        "export function pick(x: number, cb: number): number {",
        "  if (cb(1) && x > 0) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
  });

  test("a numeric ! operand records its site naming !", () => {
    const src = [
      "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
      "export function pick(x: number): number {",
      "  if (!x) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'!' models boolean operands only; the operand is not a boolean " +
        "(Identifier at 3:8)",
    ]);
  });

  test("a boolean disjunction in a numeric position is the engine's Error", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  return (x === 0 || x === 1);",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Error",
        reason:
          "'pick' could not be modeled: operator '||' yields a boolean, not a number",
      }),
    ]);
  });

  test("an unsupported operator inside a logical operand still names itself", () => {
    const src = [
      "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
      "export function pick(x: number): number {",
      "  if (!(x ** 2 === 0)) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("'**' is not supported"),
    ]);
  });

  test("a construct-failed callee inside ! travels with the call", () => {
    const src = [
      "const g = (x: number): number => x;",
      "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
      "export function pick(x: number): number {",
      "  if (!(g(x) === 0)) {",
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("'g' could not be modeled"),
    ]);
  });
});

describe("conditional expressions", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts";

  test("the -0 normalization walks to a cond node", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(canon(x), canon(x)) } */",
        "export function canon(x: number): number {",
        "  return Object.is(x, -0) ? 0 : x;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "cond",
          cond: {
            kind: "same-value",
            left: { kind: "id", name: "x" },
            right: { kind: "num", lit: "-0" },
          },
          then: { kind: "num", lit: "0" },
          else: { kind: "id", name: "x" },
        },
      },
    ]);
  });

  test("a non-boolean condition records its site naming ?:", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
      "export function pick(x: number): number {",
      "  return x ? 0 : 1;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'?:' models boolean operands only; the condition is not a boolean " +
        "(Identifier at 3:10)",
    ]);
  });

  test("an unsupported operator in an arm records its construct at the site", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
      "export function pick(x: number): number {",
      "  return x < 1 ? 0 : x ** 2;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual(["'**' is not supported"]);
  });

  test("a degraded callee in an arm records its construct at a site", () => {
    const src = [
      "export function g(x: number): number {",
      "  return x ** 2;",
      "}",
      "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
      "export function pick(x: number): number {",
      "  return x < 1 ? g(x) : 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("'**' is not supported"),
    ]);
  });

  test("a degraded member in an arm travels to a site", () => {
    const src = [
      "export class Dep {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  async gone(): number {",
      "    return 1;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
      "export function pick(x: number): number {",
      "  return x < 1 ? new Dep(1).gone() : 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining("'Dep#gone' could not be modeled"),
    ]);
  });

  test("numeric arms make a conditional an Object.is argument", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(canon(x), canon(x)) } */",
        "export function canon(x: number): number {",
        "  if (Object.is(x < 1 ? x : 0, -0)) {",
        "    return 0;",
        "  }",
        "  return x;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toMatchObject({
      kind: "if",
      cond: { kind: "same-value", left: { kind: "cond" } },
    });
  });

  test("boolean arms make a conditional a logical operand", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
        "export function pick(x: number): number {",
        "  if ((x < 1 ? x > 0 : x > 2) && x < 5) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toMatchObject({
      kind: "if",
      cond: { kind: "binop", op: "&&", left: { kind: "cond" } },
    });
  });

  test("boolean arms make a conditional a boolean Object.is argument (#209)", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
        "export function pick(x: number): number {",
        "  if (Object.is(x < 1 ? x > 0 : x > 2, -0)) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toEqual(
      expect.objectContaining({
        cond: {
          kind: "jsval-eq",
          semantics: "same-value",
          left: {
            kind: "inject",
            tag: "boolean",
            expr: expect.objectContaining({ kind: "cond" }),
          },
          right: {
            kind: "inject",
            tag: "number",
            expr: { kind: "num", lit: "-0" },
          },
        },
      }),
    );
  });

  test("a chain of conditionals nests to the right", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(sign(x), sign(x)) } */",
        "export function sign(x: number): number {",
        "  return x < 0 ? -1 : x > 0 ? 1 : 0;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)[0]).toMatchObject({
      kind: "return",
      expr: {
        kind: "cond",
        cond: { kind: "binop", op: "<" },
        then: { kind: "num", lit: "-1" },
        else: {
          kind: "cond",
          cond: { kind: "binop", op: ">" },
          then: { kind: "num", lit: "1" },
          else: { kind: "num", lit: "0" },
        },
      },
    });
  });

  test("arms that disagree with the position are the engine's error", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
        "export function pick(x: number): number {",
        "  return x < 1 ? 0 : x < 2;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Error",
        reason:
          "'pick' could not be modeled: operator '<' yields a boolean, " +
          "not a number",
      }),
    ]);
  });

  test("a conditional chooses between class-typed arguments", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
export function pull(p: Point): number {
  return p.x;
}
/** @ensures{p} forall (x: int ∈ [0, 4)) { 0 <= pick(new Point(x), new Point(x), x) } */
export function pick(a: Point, b: Point, t: number): number {
  return pull(t < 1 ? a : b);
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[2]!)[0]).toMatchObject({
      kind: "return",
      expr: {
        kind: "call",
        callee: "pull",
        args: [
          {
            kind: "cond",
            then: { kind: "id", name: "a" },
            else: { kind: "id", name: "b" },
          },
        ],
      },
    });
  });

  test("a conditional models inside a formula atom", () => {
    const { emission, classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { 0 <= keep(x < 1 ? x : 0) } */",
        "export function keep(x: number): number {",
        "  return x;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.obligations[0]!.payload).toMatchObject({
      kind: "structured",
      conclusion: {
        kind: "istrue",
        expr: { kind: "binop", op: "<=", right: { args: [{ kind: "cond" }] } },
      },
    });
  });
});

const BOX = `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */
  get v(): number {
    return this.#v;
  }
}
`;

/** The classification of the annotation on a member of a class decl. */
function classClassifiedOf(cls: string): { szs: string; reason: string } {
  const { classified } = emitModule(cls, "t.ts");
  expect(classified).toHaveLength(1);
  return { szs: classified[0]!.szs, reason: classified[0]!.reason };
}

/** A class whose sole annotation sits on a getter over field `#v`. */
function classWith(members: string): string {
  return [
    "export class C {",
    "  #v: number;",
    members,
    "  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */",
    "  get v(): number {",
    "    return this.#v;",
    "  }",
    "}",
    "",
  ].join("\n");
}

describe("class declarations (#129)", () => {
  test("a number-typed class models as a class declaration", () => {
    const { emission } = emitModule(BOX, "t.ts");
    expect(emission.declarations).toEqual([
      {
        kind: "class",
        name: "Box",
        source: expect.stringContaining("export class Box"),
        fields: [{ name: "#v" }],
        ctor: {
          params: [{ name: "v", type: "number" }],
          body: [
            { kind: "field-set", field: "#v", expr: { kind: "id", name: "v" } },
          ],
        },
        getters: [
          {
            name: "v",
            body: [
              {
                kind: "return",
                expr: {
                  kind: "field-read",
                  className: "Box",
                  field: "#v",
                  object: { kind: "self" },
                },
              },
            ],
          },
        ],
        methods: [],
      },
    ]);
  });

  test("a number field rides the wire as a name alone", () => {
    const { emission } = emitModule(BOX, "t.ts");
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.fields).toEqual([{ name: "#v" }]);
    expectValidEmission(emission);
  });

  test.each([
    [
      "assigning a field twice on one path",
      "  constructor(v: number) {\n    this.#v = v;\n    this.#v = v + 1;\n  }",
      "assigns field '#v' more than once on a path",
    ],
    [
      "assigning a field on one path only",
      "  constructor(v: number) {\n    if (v < 0) {\n      this.#v = 0;\n    }\n  }",
      "assigns field '#v' on only some paths",
    ],
    [
      "never assigning a field",
      "  constructor(v: number) {\n    if (v < 0) {\n      throw new RangeError('x');\n    }\n  }",
      "never assigns field '#v'",
    ],
  ])("%s degrades the class", (_label, ctor, fragment) => {
    const { szs, reason } = classClassifiedOf(classWith(ctor));
    expect(szs).toBe("Inappropriate");
    expect(reason).toContain(fragment);
    expect(reason).toContain(
      "the class model requires every field assigned exactly once on every path",
    );
  });

  test("a class with no constructor degrades naming the gap", () => {
    const src = classWith("");
    const { szs, reason } = classClassifiedOf(src);
    expect(szs).toBe("Inappropriate");
    expect(reason).toBe(
      "'C#v' could not be modeled: class 'C' has no constructor implementation to model",
    );
  });

  const CTOR = "  constructor(v: number) {\n    this.#v = v;\n  }";

  test("an extends clause degrades the class", () => {
    const src = [
      "class B {}",
      "export class C extends B {",
      "  #v: number;",
      CTOR,
      "  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { szs, reason } = classClassifiedOf(src);
    expect(szs).toBe("Inappropriate");
    expect(reason).toMatch(/unmapped TypeScript construct/);
  });

  test.each([
    [
      "a setter",
      classWith(`${CTOR}\n  set w(n: number) {\n    n;\n  }`),
      /unmapped TypeScript construct/,
    ],
    [
      "a non-number field",
      [
        "export class C {",
        "  #v: string;",
        "  constructor(v: string) {",
        "    this.#v = v;",
        "  }",
        "  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */",
        "  get v(): number {",
        "    return 1;",
        "  }",
        "}",
        "",
      ].join("\n"),
      /unmapped TypeScript construct 'StringKeyword'/,
    ],
    [
      "a field with an initializer",
      [
        "export class C {",
        "  #v: number = 0;",
        CTOR,
        "  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */",
        "  get v(): number {",
        "    return this.#v;",
        "  }",
        "}",
        "",
      ].join("\n"),
      /unmapped TypeScript construct/,
    ],
    [
      "a parameter property",
      [
        "export class C {",
        "  constructor(readonly v: number) {}",
        "  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */",
        "  get w(): number {",
        "    return 1;",
        "  }",
        "}",
        "",
      ].join("\n"),
      /unmapped TypeScript construct 'ReadonlyKeyword'/,
    ],
    [
      "an index signature",
      classWith(`${CTOR}\n  [k: string]: number;`),
      /unmapped TypeScript construct/,
    ],
  ])("%s degrades the class", (_label, src, pattern) => {
    const { szs, reason } = classClassifiedOf(src);
    expect(szs).toBe("Inappropriate");
    expect(reason).toMatch(pattern);
  });

  test("an unmodelable method degrades alone; the class still models", () => {
    const src = [
      "export class Box {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  /** @ensures{q} forall (x: number) { Object.is(twice(x), x) } */",
      "  async twice(n: number): number {",
      "    return n + n;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /'Box#twice' could not be modeled: unmapped TypeScript construct 'MethodDeclaration'/,
    );
    expect(emission.declarations).toHaveLength(1);
    expect(emission.declarations[0]!.kind).toBe("class");
  });

  test("a static member degrades alone; the class still models", () => {
    const src = [
      "export class Box {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  /** @ensures{q} forall (x: number) { Object.is(make(x), x) } */",
      "  static make(n: number): number {",
      "    return n;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toMatch(/'Box\.make' could not be modeled/);
    expect(emission.declarations).toHaveLength(1);
  });

  test("a getter assigning a field degrades alone as immutability", () => {
    const src = [
      "export class Box {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  /** @ensures{q} forall (x: number) { Object.is(new Box(x).bad, x) } */",
      "  get bad(): number {",
      "    this.#v = 1;",
      "    return this.#v;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toBe(
      "'Box#bad' could not be modeled: 'Box#bad' assigns field '#v' outside " +
        "the constructor; instances are immutable after construction",
    );
    const cls = emission.declarations[0]!;
    assert(cls.kind === "class");
    expect(cls.getters.map((g) => g.name)).toEqual(["v"]);
  });

  // A definite-assignment `!` says nothing the model reads: the
  // single-assignment analysis is the authority on what is assigned.
  test("a definite-assignment field still models", () => {
    const src = [
      "export class Box {",
      "  #v!: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0]!;
    assert(cls.kind === "class");
    expect(cls.fields).toEqual([{ name: "#v" }]);
  });

  test("a throwing guard with a branch assignment models", () => {
    const src = [
      "export class Gate {",
      "  #lo: number;",
      "  constructor(a: number) {",
      "    if (a < 0) {",
      "      throw new RangeError('negative');",
      "    } else {",
      "      this.#lo = a;",
      "    }",
      "  }",
      "  get lo(): number {",
      "    return this.#lo;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0]!;
    assert(cls.kind === "class");
    expect(cls.ctor.body).toEqual([
      {
        kind: "if",
        cond: {
          kind: "binop",
          op: "<",
          left: { kind: "id", name: "a" },
          right: { kind: "num", lit: "0" },
        },
        then: [{ kind: "throw", error: "RangeError" }],
        else: [
          { kind: "field-set", field: "#lo", expr: { kind: "id", name: "a" } },
        ],
      },
    ]);
  });
});

describe("builtin member reads model as the library's constants", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts"; // any resolvable path; no imports are followed

  test("a returned Number.EPSILON product walks to a builtin read", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 10)) { tiny(n) >= 0 } */",
      "export function tiny(x: number): number {",
      "  return x * Number.EPSILON;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        name: "tiny",
        body: [
          {
            kind: "return",
            expr: {
              kind: "binop",
              op: "*",
              left: { kind: "id", name: "x" },
              right: {
                kind: "builtin-read",
                object: "Number",
                member: "EPSILON",
              },
            },
          },
        ],
      }),
    ]);
  });

  test.each([
    ["Number", "EPSILON"],
    ["Number", "MAX_SAFE_INTEGER"],
    ["Number", "MIN_SAFE_INTEGER"],
    ["Number", "MAX_VALUE"],
    ["Number", "MIN_VALUE"],
    ["Number", "POSITIVE_INFINITY"],
    ["Number", "NEGATIVE_INFINITY"],
    ["Number", "NaN"],
    ["Math", "E"],
    ["Math", "LN10"],
    ["Math", "LN2"],
    ["Math", "LOG10E"],
    ["Math", "LOG2E"],
    ["Math", "PI"],
    ["Math", "SQRT1_2"],
    ["Math", "SQRT2"],
  ])("%s.%s is a whitelisted read", (object, member) => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { k(n) >= 0 } */",
      "export function k(x: number): number {",
      `  return ${object}.${member};`,
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      { kind: "return", expr: { kind: "builtin-read", object, member } },
    ]);
  });

  test("a formula atom reads Number.MAX_SAFE_INTEGER", () => {
    const src = [
      "/** @ensures{bounded} forall (n: int ∈ [0, 10)) { keep(n) <= Number.MAX_SAFE_INTEGER } */",
      "export function keep(x: number): number {",
      "  return x;",
      "}",
    ].join("\n");
    const { emission, classified } = emitModule(src, FILE);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toEqual({
      kind: "istrue",
      expr: {
        kind: "binop",
        op: "<=",
        left: {
          kind: "call",
          callee: "keep",
          args: [{ kind: "id", name: "n" }],
        },
        right: {
          kind: "builtin-read",
          object: "Number",
          member: "MAX_SAFE_INTEGER",
        },
      },
    });
  });

  test("a negated read is unary minus over the read", () => {
    const { emission } = emitModule(fnWith("-Number.EPSILON"), FILE);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "unop",
          op: "-",
          operand: {
            kind: "builtin-read",
            object: "Number",
            member: "EPSILON",
          },
        },
      },
    ]);
  });

  test("a read at a boolean position is the engine's type error", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { Math.PI }"))
        .classified,
    ).toEqual([
      [
        "Error",
        expect.stringContaining(
          "a read of 'Math.PI' yields a number, not a boolean",
        ),
      ],
    ]);
  });

  test("a parameter named Math shadows the constants in its own body", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { k(n) >= 0 } */",
      "export function k(Math: number): number {",
      "  return Math.PI;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'PropertyAccessExpression'",
      ),
    ]);
  });

  test("a local named Number shadows the constants from its declaration on", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { k(n) >= 0 } */",
      "export function k(x: number): number {",
      "  const Number = x;",
      "  return Number.EPSILON;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'PropertyAccessExpression'",
      ),
    ]);
  });

  test("a module binding of the namespace spelling shadows the constants", () => {
    const src = [
      "const Math = { PI: 3 };",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { k(n) >= 0 } */",
      "export function k(x: number): number {",
      "  return x * Math.PI;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'PropertyAccessExpression'",
      ),
    ]);
  });

  test("an unresolved import of the namespace spelling shadows the constants", () => {
    const src = [
      'import { Number } from "./nowhere.js";',
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { k(n) >= 0 } */",
      "export function k(x: number): number {",
      "  return x * Number.EPSILON;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'PropertyAccessExpression'",
      ),
    ]);
  });

  test("a shadowed namespace in a formula atom is refused too", () => {
    const src = [
      "const Number = { EPSILON: 1 };",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { k(n) <= Number.EPSILON } */",
      "export function k(x: number): number {",
      "  return x;",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "unmapped TypeScript construct 'PropertyAccessExpression'",
        ),
      }),
    ]);
  });

  test("Object.is against Number.NaN stays on the number path", () => {
    const { emission, classified } = emitModule(
      fnWith("Object.is(x, Number.NaN) ? 1 : 0"),
      FILE,
    );
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "cond",
          cond: {
            kind: "same-value",
            left: { kind: "id", name: "x" },
            right: { kind: "builtin-read", object: "Number", member: "NaN" },
          },
          then: { kind: "num", lit: "1" },
          else: { kind: "num", lit: "0" },
        },
      },
    ]);
  });

  test("an unlisted member read reports itself by name", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { arity(n) >= 0 } */",
      "export function arity(x: number): number {",
      "  return x * Number.length;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'Number.length' is not supported",
    ]);
  });

  test("an unlisted member read in a formula atom reports itself from the walk", () => {
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { f(x) <= Number.length }"),
      ).classified,
    ).toEqual([["Inappropriate", "'Number.length' is not supported"]]);
  });

  test("a call member in value position is modeled only as a callee", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { root(n) >= 0 } */",
      "export function root(x: number): number {",
      "  const sqrt = Math.sqrt;",
      "  return sqrt(x);",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'Math.sqrt' is modeled only as a callee",
      // The local binds to that site, and the model has no callables, so
      // calling it is a second shape it does not follow.
      expect.stringContaining("'sqrt' is a bound value, not a callable"),
    ]);
  });

  test("a read member called is modeled only as a read", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { circle(n) >= 0 } */",
      "export function circle(x: number): number {",
      "  return x * Math.PI();",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'Math.PI' is modeled only as a read",
    ]);
  });

  test("an unlisted read as a branch condition still names itself", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { flag(n) >= 0 } */",
      "export function flag(x: number): number {",
      "  if (Number.length) {",
      "    return 1;",
      "  }",
      "  return 0;",
      "}",
    ].join("\n");
    expect(residualConstructs(src, FILE)).toEqual([
      "'Number.length' is not supported",
    ]);
  });
});

describe("new and member access in atoms (#129)", () => {
  test("the Box roundTrip obligation structures with new and getter access", () => {
    const { emission, classified } = emitModule(BOX, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations).toEqual([
      {
        function: "Box#v",
        property: "roundTrip",
        formula: "forall (x: number) { Object.is(new Box(x).v, x) }",
        payload: {
          kind: "structured",
          binders: [{ name: "x", kind: "number" }],
          conclusion: {
            kind: "eq",
            left: {
              kind: "getter-read",
              className: "Box",
              name: "v",
              object: {
                kind: "new",
                className: "Box",
                args: [{ kind: "id", name: "x" }],
              },
            },
            right: { kind: "id", name: "x" },
          },
        },
      },
    ]);
  });

  test("a degraded class travels its reason; a healthy sibling still models", () => {
    const src = [
      "class B {}",
      "export class Wide extends B {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    return 1;",
      "  }",
      "}",
      BOX,
      "/** @ensures{wide} forall (x: number) { Object.is(new Wide(x).v, x) } */",
      "export function g(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /'Wide' could not be modeled: unmapped TypeScript construct/,
    );
    // The healthy class still structures its own obligation.
    expect(emission.obligations.map((o) => o.function)).toEqual(["Box#v"]);
  });

  test("an atom naming a degraded member travels the member's reason", () => {
    const src = [
      "export class Box {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  async twice(n: number): number {",
      "    return n + n;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "/** @ensures{p} forall (x: number) { Object.is(new Box(x).twice, x) } */",
      "export function g(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /'Box#twice' could not be modeled: unmapped TypeScript construct 'MethodDeclaration'/,
    );
  });

  /** The classification of an annotation whose atom is `formula`, on a
   * file that also declares the Box class. */
  function atomClassifiedOf(atom: string): { szs: string; reason: string } {
    const src = [
      BOX.replace(
        "  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */\n",
        "",
      ),
      `/** @ensures{p} forall (x: number) { ${atom} } */`,
      "export function g(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    return { szs: classified[0]!.szs, reason: classified[0]!.reason };
  }

  test.each([
    [
      "a wrong constructor arity",
      "Object.is(new Box(x, x).v, x)",
      "'Box' expects 1 argument(s), got 2",
    ],
    [
      "an unknown member",
      "Object.is(new Box(x).w, x)",
      "'Box' has no member 'w' in the model",
    ],
    [
      "new over a function",
      "Object.is(new g(x).v, x)",
      "'g' is not a class; 'new' has no model for it",
    ],
    [
      "a class called as a function",
      "Object.is(Box(x), x)",
      "'Box' is a class; it is only modeled under 'new'",
    ],
    [
      "a bare instance in a numeric position",
      "Object.is(new Box(x) + 1, x)",
      "'new Box(...)' yields an instance of 'Box', not a number",
    ],
  ])("%s classifies Error", (_label, atom, reason) => {
    const got = atomClassifiedOf(atom);
    expect(got.szs).toBe("Error");
    expect(got.reason).toBe(`property elaboration failed: ${reason}`);
  });

  // The conclusion is pre-scanned as written, so an instance in a side
  // meets the numbers-only refusal, same as in a body or guard.
  test("a bare instance as an equation side is refused as non-numeric", () => {
    const got = atomClassifiedOf("Object.is(new Box(x), x)");
    expect(got.szs).toBe("Inappropriate");
    expect(got.reason).toContain(
      "'Object.is' admits numbers, booleans, union values, 'undefined', " +
        "and 'null'; argument 1 is not one (NewExpression",
    );
  });

  test("a public field reads through member access", () => {
    const src = [
      "export class Cell {",
      "  readonly w: number;",
      "  constructor(v: number) {",
      "    this.w = v;",
      "  }",
      "}",
      "/** @ensures{p} forall (x: number) { Object.is(new Cell(x).w, x) } */",
      "export function g(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toEqual({
      kind: "structured",
      binders: [{ name: "x", kind: "number" }],
      conclusion: {
        kind: "eq",
        left: {
          kind: "field-read",
          className: "Cell",
          field: "w",
          object: {
            kind: "new",
            className: "Cell",
            args: [{ kind: "id", name: "x" }],
          },
        },
        right: { kind: "id", name: "x" },
      },
    });
  });

  test("a function body builds an instance too", () => {
    const src = [
      BOX.replace(
        "  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */\n",
        "",
      ),
      "export function g(x: number): number {",
      "  return new Box(x).v;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const g = emission.declarations.find((d) => declName(d) === "g")!;
    expect(fnBody(g)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "getter-read",
          className: "Box",
          name: "v",
          object: {
            kind: "new",
            className: "Box",
            args: [{ kind: "id", name: "x" }],
          },
        },
      },
    ]);
  });
});

/** A class around the standard `#v` field, its constructor, and a getter
 * `v` carrying the annotation; each part is overridable. */
function cls(opts: {
  head?: string;
  field?: string;
  ctor?: string;
  members?: string;
  getter?: string;
}): string {
  return [
    opts.head ?? "export class C {",
    opts.field ?? "  #v: number;",
    opts.ctor ?? "  constructor(v: number) {\n    this.#v = v;\n  }",
    ...(opts.members === undefined ? [] : [opts.members]),
    "  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */",
    opts.getter ?? "  get v(): number {\n    return this.#v;\n  }",
    "}",
    "",
  ].join("\n");
}

describe("class-level degrade paths (#129)", () => {
  test.each([
    ["a class decorator", { head: "@dec\nexport class C {" }],
    ["a type parameter", { head: "export class C<T> {" }],
    ["an abstract class", { head: "export abstract class C {" }],
    [
      "a member decorator",
      { members: "  @dec\n  twice(): number {\n    return 1;\n  }" },
    ],
    [
      "a string-literal member name",
      { members: '  "m"(): number {\n    return 1;\n  }' },
    ],
    ["an accessor field", { field: "  accessor #v: number;" }],
    ["an untyped field", { field: "  #v;" }],
    ["a reserved field name", { field: "  construct: number;" }],
    ["two fields of one spelling", { field: "  #v: number;\n  #v: number;" }],
    [
      "a field and a getter sharing a spelling",
      {
        field: "  #v: number;\n  v: number;",
        ctor: "  constructor(v: number) {\n    this.#v = v;\n    this.v = v;\n  }",
      },
    ],
    [
      "two constructor implementations",
      {
        ctor:
          "  constructor(v: number) {\n    this.#v = v;\n  }\n" +
          "  constructor(v: number) {\n    this.#v = v;\n  }",
      },
    ],
    [
      "a destructured constructor parameter",
      {
        field: "",
        ctor: "  constructor({ v }: { v: number }) {}",
        getter: "  get v(): number {\n    return 1;\n  }",
      },
    ],
    [
      "a rest constructor parameter",
      {
        field: "",
        ctor: "  constructor(...v: number[]) {}",
        getter: "  get v(): number {\n    return 1;\n  }",
      },
    ],
    [
      "an optional constructor parameter",
      {
        field: "",
        ctor: "  constructor(v?: number) {}",
        getter: "  get v(): number {\n    return 1;\n  }",
      },
    ],
    [
      "an untyped constructor parameter",
      {
        field: "",
        ctor: "  constructor(v) {}",
        getter: "  get v(): number {\n    return 1;\n  }",
      },
    ],
    [
      "a non-number constructor parameter",
      {
        field: "",
        ctor: "  constructor(v: string) {}",
        getter: "  get v(): number {\n    return 1;\n  }",
      },
    ],
    [
      "a statement outside the slice in the constructor",
      {
        ctor:
          "  constructor(v: number) {\n    for (;;) {}\n" +
          "    this.#v = v;\n  }",
      },
    ],
    [
      "a compound field assignment",
      { ctor: "  constructor(v: number) {\n    this.#v += v;\n  }" },
    ],
    [
      "a bodiless constructor overload beside a bad one",
      {
        ctor:
          "  constructor(v: number);\n" +
          "  constructor(v: string) {\n    this.#v = 1;\n  }",
      },
    ],
    [
      "a return in the constructor",
      {
        ctor: "  constructor(v: number) {\n    if (v < 0) {\n      return v;\n    }\n    this.#v = v;\n  }",
      },
    ],
  ])("%s degrades the class", (_label, opts) => {
    const { szs, reason } = classClassifiedOf(cls(opts));
    expect(szs).toBe("Inappropriate");
    expect(reason).toMatch(/^'C#v' could not be modeled: /);
  });

  test("an unsupported operator in the constructor records a site there", () => {
    const src = cls({
      ctor: "  constructor(v: number) {\n    this.#v = v ** 2;\n  }",
    });
    expect(residualConstructs(src)).toEqual(["'**' is not supported"]);
    expect(residualOwners(src)).toEqual(["C#constructor"]);
  });

  test("an unbound name in the constructor is the engine's Error", () => {
    const { szs, reason } = classClassifiedOf(
      cls({ ctor: "  constructor(v: number) {\n    this.#v = missing;\n  }" }),
    );
    expect(szs).toBe("Error");
    expect(reason).toBe(
      "'C#v' could not be modeled: unbound identifier 'missing'",
    );
  });

  test.each([
    [
      "a constructor that throws on every path",
      "  constructor(v: number) {\n    if (v < 0) {\n      throw new RangeError('a');\n    } else {\n      throw new RangeError('b');\n    }\n  }",
    ],
    [
      "an else arm that throws",
      "  constructor(v: number) {\n    if (v < 0) {\n      this.#v = 0;\n    } else {\n      throw new RangeError('a');\n    }\n  }",
    ],
    [
      "both arms assigning the field",
      "  constructor(v: number) {\n    if (v < 0) {\n      this.#v = 0;\n    } else {\n      this.#v = v;\n    }\n  }",
    ],
    [
      "a local reassignment beside the field set",
      "  constructor(v: number) {\n    let y = v;\n    y = v + 1;\n    this.#v = y;\n  }",
    ],
  ])("%s still models", (_label, ctor) => {
    const { emission, classified } = emitModule(cls({ ctor }), "t.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[0]!.kind).toBe("class");
  });

  test("an arm assigning only in the else degrades naming the field", () => {
    const { reason } = classClassifiedOf(
      cls({
        ctor: "  constructor(v: number) {\n    if (v < 0) {\n      v;\n    } else {\n      this.#v = v;\n    }\n  }",
      }),
    );
    expect(reason).toContain("assigns field '#v' on only some paths");
  });

  test("an annotation on a degraded class's constructor travels the class's reason", () => {
    const src = [
      "export class Counter {",
      "  readonly n: number;",
      "  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= a } */",
      "  constructor(n: string) {",
      "    this.n = 1;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(emission.obligations).toEqual([]);
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toBe(
      "'Counter#constructor' could not be modeled: unmapped TypeScript " +
        "construct 'StringKeyword' at 4:18",
    );
  });

  test("an annotation on a modeling class's constructor still structures", () => {
    const src = [
      "export class C {",
      "  #v: number;",
      "  /** @ensures{p} forall (x: number) { 0 <= 1 } */",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations.map((o) => o.function)).toEqual([
      "C#constructor",
    ]);
  });
});

describe("class member-level degrade paths (#129)", () => {
  /** The classification of the annotation on member `m`, in a file whose
   * class otherwise models. */
  function memberClassifiedOf(
    member: string,
    fn = "bad",
  ): { szs: string; reason: string; declarations: number } {
    const src = [
      "export class C {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      `  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */`,
      member,
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.annotation.functionName).toBe(fn);
    return {
      szs: classified[0]!.szs,
      reason: classified[0]!.reason,
      declarations: emission.declarations.length,
    };
  }

  test.each([
    [
      "a getter with a parameter",
      "  get bad(n: number): number {\n    return 1;\n  }",
    ],
    ["a bodiless getter", "  get bad(): number;"],
    ["an untyped getter", "  get bad() {\n    return 1;\n  }"],
    ["a non-number getter", '  get bad(): string {\n    return "x";\n  }'],
    [
      "a getter reading a non-field",
      "  get bad(): number {\n    return this.other;\n  }",
    ],
    ["a getter that can run off the end", "  get bad(): number {}"],
    [
      // A bare expression statement is a discard now, so the case that
      // still degrades a getter alone is a statement kind outside the slice.
      "a statement outside the slice in a getter",
      "  get bad(): number {\n    for (;;) {}\n    return this.#v;\n  }",
    ],
    [
      "a getter writing a name that is not a field",
      "  get bad(): number {\n    this.other = 1;\n    return this.#v;\n  }",
    ],
    [
      "a non-block arm writing a field",
      "  get bad(): number {\n    if (this.#v < 0) this.#v = 1;\n    return this.#v;\n  }",
    ],
  ])("%s degrades alone", (_label, member) => {
    const got = memberClassifiedOf(member);
    expect(got.declarations).toBe(1);
  });

  test("an unsupported operator in a getter records a site there", () => {
    const src = [
      "export class C {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  /** @ensures{p} forall (x: number) { Object.is(new C(x).v, x) } */",
      "  get bad(): number {",
      "    return this.#v ** 2;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src)).toEqual(["'**' is not supported"]);
    expect(residualOwners(src)).toEqual(["C#bad"]);
  });

  test("a reserved getter name degrades alone", () => {
    const got = memberClassifiedOf(
      "  get mk(): number {\n    return 1;\n  }",
      "mk",
    );
    expect(got.szs).toBe("Inappropriate");
    expect(got.reason).toContain("reserves the name 'mk'");
    expect(got.declarations).toBe(1);
  });

  // The extractor attaches no annotation to a private member, so their
  // absence from the model is what there is to check.
  test("private getters are absent from the model", () => {
    const src = [
      "export class C {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get #p(): number {",
      "    return this.#v;",
      "  }",
      "  private get q(): number {",
      "    return this.#v;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const c = emission.declarations[0]!;
    assert(c.kind === "class");
    expect(c.getters.map((g) => g.name)).toEqual(["v"]);
  });

  test.each([
    [
      "an arm-assigned field",
      "  get bad(): number {\n    if (this.#v < 0) {\n      this.#v = 1;\n    }\n    return this.#v;\n  }",
    ],
    [
      "an else-assigned field",
      "  get bad(): number {\n    if (this.#v < 0) {\n      return 1;\n    } else {\n      this.#v = 1;\n    }\n    return this.#v;\n  }",
    ],
  ])("%s degrades as immutability", (_label, member) => {
    const got = memberClassifiedOf(member);
    expect(got.reason).toContain("outside the constructor");
    expect(got.declarations).toBe(1);
  });

  test("a branching getter that writes nothing still models", () => {
    const src = [
      "export class C {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    if (this.#v < 0) {",
      "      return 1;",
      "    }",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const c = emission.declarations[0]!;
    assert(c.kind === "class");
    expect(c.getters).toHaveLength(1);
  });
});

describe("instance atoms outside the happy path (#129)", () => {
  const BOX_DECL = [
    "export class Box {",
    "  #v: number;",
    "  constructor(v: number) {",
    "    this.#v = v;",
    "  }",
    "  get v(): number {",
    "    return this.#v;",
    "  }",
    "}",
  ].join("\n");

  /** The classification of an annotation whose atom is `atom`, on a file
   * that also declares Box and a modeled function `g`. */
  function atomOf(atom: string, extra = ""): { szs: string; reason: string } {
    const src = [
      BOX_DECL,
      extra,
      `/** @ensures{p} forall (x: number) { ${atom} } */`,
      "export function g(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    return { szs: classified[0]!.szs, reason: classified[0]!.reason };
  }

  test.each([
    // A side that is not numeric-shaped meets the refusal before the walk
    // reaches whatever construct sits inside it, in every position.
    [
      "a private member on an instance",
      "Object.is(new Box(x).#v, x)",
      /'Object\.is' admits numbers, booleans, union values/,
    ],
    [
      "a type argument on new",
      "Object.is(new Box<number>(x).v, x)",
      /unmapped TypeScript construct 'NumberKeyword'/,
    ],
    [
      "an opaque construct in a new argument",
      "Object.is(new Box(await h(x)).v, x)",
      /unmapped TypeScript construct 'AwaitExpression'/,
    ],
    [
      "an unsupported operator in a new argument",
      "Object.is(new Box(x ** 2).v, x)",
      /'\*\*' is not supported/,
    ],
    [
      "a qualified constructor name",
      "Object.is(new a.B(x).v, x)",
      /'Object\.is' admits numbers, booleans, union values/,
    ],
  ])("%s classifies Inappropriate", (_label, atom, pattern) => {
    const got = atomOf(atom);
    expect(got.szs).toBe("Inappropriate");
    expect(got.reason).toMatch(pattern);
  });

  const WIDE = [
    "class Base {}",
    "export class Wide extends Base {",
    "  #v: number;",
    "  constructor(v: number) {",
    "    this.#v = v;",
    "  }",
    "  get v(): number {",
    "    return this.#v;",
    "  }",
    "}",
  ].join("\n");

  test.each([
    ["nested in a new argument", "Object.is(new Box(new Wide(x).v).v, x)"],
    ["nested in a call argument", "Object.is(g(new Wide(x).v), x)"],
  ])("a degraded class %s still travels", (_label, atom) => {
    const got = atomOf(atom, WIDE);
    expect(got.szs).toBe("Inappropriate");
    expect(got.reason).toMatch(/'Wide' could not be modeled/);
  });

  test.each([
    [
      "new over a degraded declaration",
      "Object.is(new bad(x).v, x)",
      "'bad' has no model: unbound identifier 'missing'",
      "export function bad(n: number): number {\n  return missing;\n}",
    ],
    [
      "new over an unknown name",
      "Object.is(new Nope(x).v, x)",
      "no model registered for 'Nope'",
      "",
    ],
    [
      "new over a bound variable",
      "Object.is(new x(1).v, x)",
      "'x' is not a class; 'new' has no model for it",
      "",
    ],
  ])("%s classifies Error", (_label, atom, reason, extra) => {
    const got = atomOf(atom, extra);
    expect(got.szs).toBe("Error");
    expect(got.reason).toBe(`property elaboration failed: ${reason}`);
  });

  // `new C` with no argument list is still a construction; the arity
  // check is what refuses it.
  test("an argument-less new is an arity mismatch", () => {
    const got = atomOf("Object.is((new Box).v, x)");
    expect(got.szs).toBe("Error");
    expect(got.reason).toBe(
      "property elaboration failed: 'Box' expects 1 argument(s), got 0",
    );
  });

  test("a member read in a boolean position is a type mismatch", () => {
    const got = atomOf("new Box(x).v");
    expect(got.szs).toBe("Error");
    expect(got.reason).toBe(
      "property elaboration failed: a member read yields a number, not a boolean",
    );
  });

  test("a body's Object.is compares a member read", () => {
    const src = [
      BOX_DECL,
      "/** @ensures{p} forall (x: number) { Object.is(pick(x), 0) } */",
      "export function pick(x: number): number {",
      "  if (Object.is(new Box(x).v, 0)) {",
      "    return 1;",
      "  }",
      "  return 0;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const pick = emission.declarations.find((d) => declName(d) === "pick")!;
    expect(JSON.stringify(fnBody(pick))).toContain('"kind":"getter-read"');
  });

  test("a body naming a degraded class travels its reason", () => {
    const src = [
      WIDE,
      "/** @ensures{p} forall (x: number) { Object.is(use(x), x) } */",
      "export function use(x: number): number {",
      "  return new Wide(x).v;",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(/'Wide' could not be modeled/),
    ]);
  });

  test("a getter's Object.is compares a field read", () => {
    const src = [
      "export class C {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    if (Object.is(this.#v, 0)) {",
      "      return 1;",
      "    }",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const c = emission.declarations[0]!;
    assert(c.kind === "class");
    expect(JSON.stringify(c.getters[0]!.body)).toContain('"kind":"same-value"');
  });
});

describe("instance methods (#130)", () => {
  const boxWith = (member: string) => `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  ${member}
}
`;

  test("a method models as an instance function with its parameters", () => {
    const src = boxWith(`scale(k: number): number {
    return this.#v * k;
  }`);
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0]!;
    expect(cls.kind).toBe("class");
    expect((cls as EmitClass).methods).toEqual([
      {
        name: "scale",
        params: [{ name: "k", type: "number" }],
        body: [
          {
            kind: "return",
            expr: {
              kind: "binop",
              op: "*",
              left: {
                kind: "field-read",
                className: "Box",
                field: "#v",
                object: { kind: "self" },
              },
              right: { kind: "id", name: "k" },
            },
          },
        ],
      },
    ]);
  });

  test("an annotation on a modeled method joins by its qualified name", () => {
    const src = boxWith(`/** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  scale(k: number): number {
    return this.#v * k;
  }`);
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.function).toBe("Box#scale");
  });

  test.each([
    ["#hidden(): number {\n    return 1;\n  }", "PrivateIdentifier"],
    ["private hidden(): number {\n    return 1;\n  }", "PrivateIdentifier"],
    ["async m(): number {\n    return 1;\n  }", "MethodDeclaration"],
    ["*m(): number {\n    return 1;\n  }", "MethodDeclaration"],
    ["m<T>(): number {\n    return 1;\n  }", "TypeParameter"],
    ["m(x: string): number {\n    return 1;\n  }", "StringKeyword"],
    ["m(x?: number, y: number): number {\n    return 1;\n  }", "Parameter"],
    ["m(...xs: number[]): number {\n    return 1;\n  }", "DotDotDotToken"],
    ["m(x: number): string {\n    return 'a';\n  }", "StringKeyword"],
    ["m(x: number) {\n    return 1;\n  }", "MethodDeclaration"],
  ])("a method outside the slice degrades alone: %s", (member) => {
    const src = boxWith(`/** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  get v(): number {
    return this.#v;
  }
  ${member}`);
    const { classified, emission } = emitModule(src, "t.ts");
    // The sibling getter still models and its annotation still emits.
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
    expect((emission.declarations[0] as EmitClass).methods).toEqual([]);
  });

  test("a degraded method's reason travels to its own annotation", () => {
    const src = boxWith(`/** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  async m(): number {
    return 1;
  }`);
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /'Box#m' could not be modeled: unmapped TypeScript construct/,
    );
  });

  test("a reserved method name degrades alone", () => {
    const src = boxWith(`construct(): number {
    return 1;
  }`);
    const { emission } = emitModule(src, "t.ts");
    expect((emission.declarations[0] as EmitClass).methods).toEqual([]);
  });

  test("a method that writes a field degrades alone", () => {
    const src = boxWith(`m(x: number): number {
    this.#v = x;
    return x;
  }`);
    const { emission } = emitModule(src, "t.ts");
    expect((emission.declarations[0] as EmitClass).methods).toEqual([]);
    // Reuses the getter's immutability reason via the same degrade path.
  });

  test("a bodiless overload signature never blocks the implementation", () => {
    const src = boxWith(`m(x: number): number;
  m(x: number): number {
    return x;
  }`);
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect((emission.declarations[0] as EmitClass).methods).toHaveLength(1);
  });

  test("a method colliding with a field degrades the class", () => {
    const src = `export class Box {
  v: number;
  constructor(v: number) {
    this.v = v;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  v(): number {
    return 1;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toContain(
      "declares both a field and a method named",
    );
  });

  test("a method assigning its parameter models with a mutable local", () => {
    const src = boxWith(`clamp(x: number): number {
    if (x < 0) {
      x = 0;
    }
    return x + this.#v;
  }`);
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect((emission.declarations[0] as EmitClass).methods).toHaveLength(1);
  });
});

describe("method calls in atoms and bodies (#130)", () => {
  /** The Box class with `annotation` carried on its `double` method. */
  const box = (annotation: string) => `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** ${annotation} */
  double(): number {
    return this.#v * 2;
  }
}
`;

  test("a method call on a fresh instance walks in an atom", () => {
    const src = box(
      "@ensures{doubled} forall (x: number) { Object.is(new Box(x).double(), x * 2) }",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    expect(payload).toMatchObject({
      kind: "structured",
      conclusion: {
        kind: "eq",
        left: {
          kind: "method-call",
          className: "Box",
          name: "double",
          object: {
            kind: "new",
            className: "Box",
            args: [{ kind: "id", name: "x" }],
          },
          args: [],
        },
      },
    });
  });

  test("a method calls an earlier method through this", () => {
    const src = `export class Doubler {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  base(): number {
    return this.#v;
  }
  twice(): number {
    return this.base() + this.base();
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods.map((m) => m.name)).toEqual(["base", "twice"]);
    expect(cls.methods[1]!.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "binop",
        op: "+",
        left: {
          kind: "method-call",
          className: "Doubler",
          name: "base",
          object: { kind: "self" },
          args: [],
        },
        right: {
          kind: "method-call",
          className: "Doubler",
          name: "base",
          object: { kind: "self" },
          args: [],
        },
      },
    });
  });

  test("a forward this-call degrades the caller alone", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  twice(): number {
    return this.base() + this.base();
  }
  base(): number {
    return this.#v;
  }
}
`;
    const { emission } = emitModule(src, "t.ts");
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods.map((m) => m.name)).toEqual(["base"]);
  });

  test("a getter calling a method degrades the getter alone", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  get d(): number {
    return this.m();
  }
  m(): number {
    return this.#v;
  }
}
`;
    const { emission } = emitModule(src, "t.ts");
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.getters).toEqual([]);
    expect(cls.methods.map((m) => m.name)).toEqual(["m"]);
  });

  test("a self-recursive method degrades alone", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  loop(): number {
    return this.loop();
  }
}
`;
    const { emission } = emitModule(src, "t.ts");
    expect((emission.declarations[0] as EmitClass).methods).toEqual([]);
  });

  test("method arity is checked in atoms", () => {
    const src = box(
      "@ensures{p} forall (x: number) { Object.is(new Box(x).double(1), x) }",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toContain("expects 0 argument(s), got 1");
  });

  test("an unknown method is the engine's error", () => {
    const src = box(
      "@ensures{p} forall (x: number) { Object.is(new Box(x).triple(), x) }",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toContain(
      "has no method 'triple' in the model",
    );
  });

  test("an atom calling a degraded method carries its reason", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  async m(): number {
    return 1;
  }
  /** @ensures{p} forall (x: number) { Object.is(new C(x).m(), x) } */
  get v(): number {
    return this.#v;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'C#m' could not be modeled");
  });

  test("a class named Math resolves to the method, not the builtin", () => {
    const src = `export class Math {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{own} forall (x: number) { Object.is(new Math(x).abs(), x) } */
  abs(): number {
    return this.#v;
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toMatchObject({
      kind: "structured",
      conclusion: {
        kind: "eq",
        left: { kind: "method-call", className: "Math", name: "abs" },
      },
    });
  });

  test("a shadowing binding still declines the builtin inside a method body", () => {
    // `Number` is a parameter, so `Number.isNaN` cannot be the builtin; the
    // call has no model and the method degrades alone, never silently
    // becoming Float.isNaN.
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  m(Number: number): number {
    if (Number.isNaN(Number)) {
      return 0;
    }
    return Number;
  }
  get v(): number {
    return this.#v;
  }
}
`;
    const { emission } = emitModule(src, "t.ts");
    const cls = emission.declarations.find(
      (d) => d.kind === "class",
    ) as EmitClass;
    expect(cls.getters.map((g) => g.name)).toEqual(["v"]);
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("receiver arguments walk before call arguments", () => {
    const src = `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: number) (y: number) { Object.is(new Box(x).plus(y), x + y) } */
  plus(y: number): number {
    return this.#v + y;
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const left = (emission.obligations[0]!.payload as any).conclusion.left;
    expect(left.object.args).toEqual([{ kind: "id", name: "x" }]);
    expect(left.args).toEqual([{ kind: "id", name: "y" }]);
  });
});

describe("getter reads on this", () => {
  const boxWith = (members: string) => `export class Box {
  readonly v: number;
  constructor(v: number) {
    this.v = v;
  }
${members}
}
`;

  test("a method reads its own class's getter through this", () => {
    const src = boxWith(`  get twice(): number {
    return this.v * 2;
  }
  /** @ensures{viaThis} forall (a: number) { Object.is(new Box(a).direct(), a * 2) } */
  direct(): number {
    return this.twice;
  }`);
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods[0]!.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "getter-read",
        className: "Box",
        name: "twice",
        object: { kind: "self" },
      },
    });
  });

  test("a method reads a getter declared after it", () => {
    const src =
      boxWith(`  /** @ensures{p} forall (a: number) { Object.is(new Box(a).direct(), a * 2) } */
  direct(): number {
    return this.later;
  }
  get later(): number {
    return this.v * 2;
  }`);
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.getters.map((g) => g.name)).toEqual(["later"]);
    expect(cls.methods.map((m) => m.name)).toEqual(["direct"]);
  });

  test("a getter reads an earlier getter through this", () => {
    const src = boxWith(`  get twice(): number {
    return this.v * 2;
  }
  get quad(): number {
    return this.twice * 2;
  }`);
    const { emission } = emitModule(src, "t.ts");
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.getters.map((g) => g.name)).toEqual(["twice", "quad"]);
    expect(JSON.stringify(cls.getters[1]!.body)).toContain(
      '{"kind":"getter-read","className":"Box","name":"twice","object":{"kind":"self"}}',
    );
  });

  test("a forward getter read through this degrades the reader alone", () => {
    const src = boxWith(`  get quad(): number {
    return this.twice * 2;
  }
  get twice(): number {
    return this.v * 2;
  }`);
    const { emission } = emitModule(src, "t.ts");
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.getters.map((g) => g.name)).toEqual(["twice"]);
  });

  test("a self-recursive getter degrades alone", () => {
    const src = boxWith(`  get loop(): number {
    return this.loop;
  }`);
    const { emission } = emitModule(src, "t.ts");
    expect((emission.declarations[0] as EmitClass).getters).toEqual([]);
  });

  test("an earlier getter's unmodelable reads are its own sites", () => {
    const src = boxWith(`  get gone(): number {
    const q = [1];
    return q[0];
  }
  /** @ensures{p} forall (a: number) { Object.is(new Box(a).direct(), a * 2) } */
  direct(): number {
    return this.gone;
  }`);
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(
        /^unmapped TypeScript construct 'ArrayLiteralExpression' at \d+:\d+$/,
      ),
      expect.stringMatching(
        /^unmapped TypeScript construct 'ElementAccessExpression' at \d+:\d+$/,
      ),
    ]);
    expect(residualOwners(src)).toEqual(["Box#gone", "Box#gone"]);
  });
});

describe("method-call scanning and misuse (#130)", () => {
  /** A class whose `plus` method the later members exercise. */
  const withPlus = (members: string) => `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  plus(y: number): number {
    return this.#v + y;
  }
  ${members}
}
`;

  test("a this-call passes its arguments through the walk", () => {
    const { emission, classified } = emitModule(
      withPlus(`sum(a: number): number {
    return this.plus(a + 1);
  }`),
      "t.ts",
    );
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods[1]!.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "method-call",
        className: "C",
        name: "plus",
        object: { kind: "self" },
        args: [
          {
            kind: "binop",
            op: "+",
            left: { kind: "id", name: "a" },
            right: { kind: "num", lit: "1" },
          },
        ],
      },
    });
  });

  test("a degraded callee inside a this-call argument travels", () => {
    const src = `export function bad(x: number) {
  return x;
}
export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  plus(y: number): number {
    return this.#v + y;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  sum(a: number): number {
    return this.plus(bad(a));
  }
}
`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("'bad' could not be modeled"),
    ]);
  });

  test("a this-call with the wrong arity degrades the caller alone", () => {
    const { emission } = emitModule(
      withPlus(`sum(a: number): number {
    return this.plus(a, a);
  }`),
      "t.ts",
    );
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods.map((m) => m.name)).toEqual(["plus"]);
  });

  test("a this-call in a boolean position is a site in the caller", () => {
    const src = withPlus(`pick(a: number): number {
    if (this.plus(a)) {
      return 0;
    }
    return 1;
  }`);
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(
        /^unmapped TypeScript construct 'CallExpression' at \d+:\d+$/,
      ),
    ]);
    expect(residualOwners(src)).toEqual(["C#pick"]);
  });

  test("an instance-call receiver's constructor arity is checked", () => {
    const src = `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: number) { Object.is(new Box(x, 1).double(), x) } */
  double(): number {
    return this.#v * 2;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toContain(
      "'Box' expects 1 argument(s), got 2",
    );
  });

  test("an opaque construct inside a call's receiver or arguments refuses", () => {
    const box = `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  plus(y: number): number {
    return this.#v + y;
  }
}
`;
    for (const atom of [
      "Object.is(new Box(`a`).plus(x), x)",
      "Object.is(new Box(x).plus(`a`), x)",
    ]) {
      const src = `/** @ensures{p} forall (x: number) { ${atom} } */
export function keep(x: number): number {
  return x;
}
${box}`;
      const { classified } = emitModule(src, "t.ts");
      expect(classified[0]!.szs).toBe("Inappropriate");
      expect(classified[0]!.reason).toContain("unmapped TypeScript construct");
    }
  });

  test("an unsupported operator inside a call's receiver or arguments refuses", () => {
    const box = `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  plus(y: number): number {
    return this.#v + y;
  }
}
`;
    for (const atom of [
      "Object.is(new Box(x ** 2).plus(x), x)",
      "Object.is(new Box(x).plus(x ** 2), x)",
    ]) {
      const src = `/** @ensures{p} forall (x: number) { ${atom} } */
export function keep(x: number): number {
  return x;
}
${box}`;
      const { classified } = emitModule(src, "t.ts");
      expect(classified[0]!.szs).toBe("Inappropriate");
      expect(classified[0]!.reason).toContain("'**'");
    }
  });

  test("a degraded member inside an instance call's arguments travels", () => {
    const src = `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  async gone(): number {
    return 1;
  }
  plus(y: number): number {
    return this.#v + y;
  }
}
/** @ensures{p} forall (x: number) { Object.is(new Box(x).plus(new Box(x).gone()), x) } */
export function keep(x: number): number {
  return x;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'Box#gone' could not be modeled");
  });

  test("a method with no implementation degrades alone", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  gone(x: number): number;
  get v(): number {
    return this.#v;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toContain(
      "'C#gone' has no implementation to model",
    );
  });

  test.each([
    [
      "a getter and a method",
      "get m(): number {\n    return 1;\n  }\n  m(): number {\n    return 1;\n  }",
      "declares both a getter and a method named",
    ],
    [
      "two methods",
      "m(): number {\n    return 1;\n  }\n  m(): number {\n    return 2;\n  }",
      "declares two methods named",
    ],
  ])("%s of one name degrades the class", (_label, members, fragment) => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  ${members}
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toContain(fragment);
  });

  test("a method that can run off the end degrades alone", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  m(x: number): number {
    if (x < 0) {
      return 0;
    }
  }
}
`;
    const { classified, emission } = emitModule(src, "t.ts");
    expect((emission.declarations[0] as EmitClass).methods).toEqual([]);
    expect(classified[0]!.reason).toContain("must return on every path");
  });

  test("an optional method degrades alone", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  m?(): number {
    return 1;
  }
  get v(): number {
    return this.#v;
  }
}
`;
    const { emission } = emitModule(src, "t.ts");
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods).toEqual([]);
    expect(cls.getters.map((g) => g.name)).toEqual(["v"]);
  });
});

describe("method-call scanner recursion (#130)", () => {
  /** A class with one degraded method (`gone`) and one modeled one. */
  const withGone = (members: string) => `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  async gone(): number {
    return 1;
  }
  plus(y: number): number {
    return this.#v + y;
  }
  ${members}
}
`;

  test("an opaque construct in a this-call argument is a site in the caller", () => {
    const src = withGone("sum(): number {\n    return this.plus(`a`);\n  }");
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'NoSubstitutionTemplateLiteral'",
      ),
    ]);
    expect(residualOwners(src)).toEqual(["C#sum"]);
  });

  test("a this-call to a degraded sibling travels the sibling's reason", () => {
    const src = withGone(`/** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  use(): number {
    return this.gone();
  }`);
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining(
        "'C#gone' could not be modeled: unmapped TypeScript construct 'MethodDeclaration'",
      ),
    ]);
  });

  test("a this-call to a later degraded sibling stays the engine's error", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  use(): number {
    return this.gone();
  }
  async gone(): number {
    return 1;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toContain(
      "'this.gone' does not name a modeled method of 'C'",
    );
  });

  test("a member's sites taint its readers in and out of the class", () => {
    const src = `export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  get bad(): number {
    const q = [1];
    return q[0];
  }
  /** @ensures{fromInside} forall (a: int ∈ [0, 10)) { Object.is(new Point(a).use(new Point(a)), 0) } */
  use(other: Point): number {
    return other.bad;
  }
}

/** @ensures{fromOutside} forall (a: int ∈ [0, 10)) { Object.is(readBad(new Point(a)), 0) } */
export function readBad(p: Point): number {
  return p.bad;
}
`;
    expect(residualOwners(src)).toEqual(["Point#bad", "Point#bad"]);
    const { emission } = emitModule(src, "t.ts");
    expect(emission.obligations).toHaveLength(2);
    const cls = emission.declarations.find(
      (d) => d.kind === "class",
    ) as EmitClass;
    expect(cls.methods[0]!.noncomputable).toBe(true);
    const readBad = emission.declarations.find(
      (d) => d.kind === "function" && d.name === "readBad",
    );
    assert(readBad?.kind === "function");
    expect(readBad.noncomputable).toBe(true);
  });

  test("a degraded member inside a this-call argument travels", () => {
    const src = `export class Dep {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  async gone(): number {
    return 1;
  }
  get v(): number {
    return this.#v;
  }
}
export class Use {
  #w: number;
  constructor(w: number) {
    this.#w = w;
  }
  plus(y: number): number {
    return this.#w + y;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  use(): number {
    return this.plus(new Dep(1).gone());
  }
}
`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("'Dep#gone' could not be modeled"),
    ]);
  });

  test("a degraded member inside a receiver's arguments travels", () => {
    const src =
      withGone("") +
      `/** @ensures{p} forall (x: number) { Object.is(new C(new C(x).gone()).plus(x), x) } */
export function keep(x: number): number {
  return x;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'C#gone' could not be modeled");
  });

  test("a branch may compare method calls with Object.is", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  plus(y: number): number {
    return this.#v + y;
  }
  pick(a: number): number {
    if (Object.is(this.plus(a), a)) {
      return 0;
    }
    return 1;
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods.map((m) => m.name)).toEqual(["plus", "pick"]);
  });

  test("a private method is not a call the model reads", () => {
    const src = `export class C {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  #hidden(): number {
    return 1;
  }
  /** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  use(): number {
    return new C(1).#hidden();
  }
}
`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'CallExpression'"),
    ]);
  });

  test("a receiver built with no argument list is still arity-checked", () => {
    const src = `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: number) { Object.is((new Box).double(), x) } */
  double(): number {
    return this.#v * 2;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toContain(
      "'Box' expects 1 argument(s), got 0",
    );
  });

  test("a member body may still read a member off a fresh instance", () => {
    const src = `export class Src {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  get v(): number {
    return this.#v;
  }
}
export class Use {
  #w: number;
  constructor(w: number) {
    this.#w = w;
  }
  borrow(): number {
    return new Src(1).v;
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const use = emission.declarations[1] as EmitClass;
    expect(use.methods[0]!.body[0]).toMatchObject({
      kind: "return",
      expr: { kind: "getter-read", className: "Src", name: "v" },
    });
  });
});

describe("a constructor with a defaulted parameter", () => {
  const src = (call: string) => `export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { ${call}.span() >= 0 } */
  span(): number {
    return this.x * this.x + this.y * this.y;
  }
}
`;
  test("the constructor is typed at the boundary and opens on the default", () => {
    const { classified, emission } = emitModule(src("new P(a, a)"), "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0];
    assert(cls?.kind === "class");
    expect(cls.ctor.params).toEqual([
      { name: "x", type: "number" },
      { name: "y", type: ["number", "undefined"] },
    ]);
    expect(cls.ctor.body[0]).toMatchObject({
      kind: "const",
      name: "y",
      init: { kind: "cond", then: { kind: "num", lit: "0" } },
    });
  });

  test("an omitted defaulted argument injects undefined in an atom", () => {
    const { classified, emission } = emitModule(src("new P(a)"), "t.ts");
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toMatchObject({
      expr: {
        left: {
          object: {
            kind: "new",
            className: "P",
            args: [
              { kind: "id", name: "a" },
              { kind: "inject", tag: "undefined" },
            ],
          },
        },
      },
    });
  });

  test("an explicit undefined in a body injects the same and travels nowhere", () => {
    const body = `export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */
export function g(a: number): number {
  return new P(a, undefined).x;
}
`;
    const { classified, emission } = emitModule(body, "t.ts");
    expect(classified).toEqual([]);
    const g = emission.declarations[1];
    assert(g?.kind === "function");
    expect(g.body[0]).toMatchObject({
      expr: {
        kind: "field-read",
        object: {
          kind: "new",
          args: [expect.anything(), { kind: "inject", tag: "undefined" }],
        },
      },
    });
  });

  test("below the minimum is an invariant, as a range", () => {
    expect(classifications(src("new P()")).classified).toEqual([
      [
        "Error",
        "property elaboration failed: 'P' expects 1 to 2 argument(s), got 0",
      ],
    ]);
  });

  test("a constructor default reading this refuses with a construct", () => {
    const bad = `export class Q {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = this.x) {
    this.x = x;
    this.y = y;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { new Q(a).z >= 0 } */
  get z(): number {
    return this.y;
  }
}
`;
    expect(residualConstructs(bad)).toEqual([
      "parameter 'y' has a default the model cannot evaluate: unmapped " +
        "TypeScript construct 'PropertyAccessExpression' at 4:38",
    ]);
  });

  test("a declared union without a default keeps the constructor's refusal", () => {
    const bad = `export class R {
  readonly x: number;
  constructor(x: number | undefined) {
    this.x = 1;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { new R(a).x >= 0 } */
  get z(): number {
    return this.x;
  }
}
`;
    const [first] = classifications(bad).classified;
    expect(first![0]).toBe("Inappropriate");
    expect(first![1]).toContain("UnionType");
  });
});

describe("a class binder over a class with a defaulted constructor parameter", () => {
  const src = `export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}
/** @ensures{p} forall (p: P) { span(p) >= 0 } */
export function span(p: P): number {
  return p.x * p.x + p.y * p.y;
}
`;

  test("the binder tree marks the defaulted parameter and quantifies over numbers", () => {
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.binders).toEqual([
      {
        name: "p",
        kind: "class",
        className: "P",
        ctorParams: [
          { name: "x", kind: "number" },
          { name: "y", kind: "number", defaulted: true },
        ],
      },
    ]);
  });
});

describe("a method with a defaulted parameter", () => {
  const src = `export class C {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { ${"%CALL%"} >= 0 } */
  plus(k: number = 1): number {
    return this.x + k;
  }
}
`;
  test("an omitted defaulted argument injects undefined at the slot", () => {
    const { classified, emission } = emitModule(
      src.replace("%CALL%", "new C(a).plus()"),
      "t.ts",
    );
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toMatchObject({
      expr: {
        left: {
          kind: "method-call",
          name: "plus",
          args: [{ kind: "inject", tag: "undefined" }],
        },
      },
    });
  });

  test("an explicit undefined injects the same", () => {
    const { classified, emission } = emitModule(
      src.replace("%CALL%", "new C(a).plus(undefined)"),
      "t.ts",
    );
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toMatchObject({
      expr: { left: { args: [{ kind: "inject", tag: "undefined" }] } },
    });
  });

  test("a supplied argument injects at the number tag", () => {
    const { emission } = emitModule(
      src.replace("%CALL%", "new C(a).plus(a)"),
      "t.ts",
    );
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toMatchObject({
      expr: {
        left: {
          args: [
            { kind: "inject", tag: "number", expr: { kind: "id", name: "a" } },
          ],
        },
      },
    });
  });

  test("over-arity is the engine's error, as a range", () => {
    const { classified } = emitModule(
      src.replace("%CALL%", "new C(a).plus(a, a)"),
      "t.ts",
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "property elaboration failed: 'C#plus' expects 0 to 1 argument(s), got 2",
      ],
    ]);
  });
});

describe("a free function with a defaulted parameter", () => {
  const ADD =
    "export function add(x: number, y: number = 0): number {\n" +
    "  return x + y;\n}\n";

  test("a call omitting the default injects undefined", () => {
    const src =
      ADD +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */\n" +
      "export function g(a: number): number { return add(a); }\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const g = emission.declarations[1];
    assert(g?.kind === "function");
    expect(g.body[0]).toMatchObject({
      expr: {
        kind: "call",
        callee: "add",
        args: [
          { kind: "id", name: "a" },
          { kind: "inject", tag: "undefined" },
        ],
      },
    });
  });

  test("a union variable admitting undefined flows to the slot", () => {
    const src =
      ADD +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a, undefined) >= 0 } */\n" +
      "export function g(a: number, u: number | undefined): number { return add(a, u); }\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const g = emission.declarations[1];
    assert(g?.kind === "function");
    expect(g.body[0]).toMatchObject({
      expr: {
        args: [
          { kind: "id", name: "a" },
          { kind: "id", name: "u" },
        ],
      },
    });
  });

  test("a non-trailing default takes an explicit undefined", () => {
    const src =
      "export function f(x: number = 1, y: number): number { return x + y; }\n" +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */\n" +
      "export function g(a: number): number { return f(undefined, a); }\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const g = emission.declarations[1];
    assert(g?.kind === "function");
    expect(g.body[0]).toMatchObject({
      expr: {
        args: [
          { kind: "inject", tag: "undefined" },
          { kind: "id", name: "a" },
        ],
      },
    });
  });

  test("under the minimum is the engine's error", () => {
    const src =
      ADD +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */\n" +
      "export function g(a: number): number { return add(); }\n";
    expect(classifications(src).classified).toEqual([
      [
        "Error",
        "'g' could not be modeled: 'add' expects 1 to 2 argument(s), got 0",
      ],
    ]);
  });
});

describe("a defaulted parameter's slot type", () => {
  test("a defaulted number parameter is typed number-or-undefined on the wire", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { add(a, a) >= 0 } */\n" +
      "export function add(x: number, y: number = 0): number {\n" +
      "  return x + y;\n}\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.params).toEqual([
      { name: "x", type: "number" },
      { name: "y", type: ["number", "undefined"] },
    ]);
  });

  test("a defaulted keyword-union parameter adds undefined once, normalized", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a, a) >= 0 } */\n" +
      "export function f(x: number, y: undefined | number | null = 0): number {\n" +
      "  return x;\n}\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.params[1]).toEqual({
      name: "y",
      type: ["number", "undefined", "null"],
    });
  });
});

describe("an instance-typed default", () => {
  const POINT = `export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
`;

  test("the parameter is an option slot and the body opens on it", () => {
    const src =
      POINT +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */\n" +
      "export function g(a: number, p: Pt = new Pt(1)): number {\n" +
      "  return a + p.x;\n}\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const g = emission.declarations[1];
    assert(g?.kind === "function");
    expect(g.params[1]).toEqual({
      name: "p",
      type: { option: { class: "Pt" } },
    });
    expect(g.body[0]).toEqual({
      kind: "const",
      name: "p",
      type: { class: "Pt" },
      init: {
        kind: "cond",
        cond: {
          kind: "option-test",
          expr: { kind: "id", name: "p" },
          present: false,
        },
        then: {
          kind: "new",
          className: "Pt",
          args: [{ kind: "num", lit: "1" }],
        },
        else: { kind: "option-get", expr: { kind: "id", name: "p" } },
      },
    });
  });

  test("an omitted, an explicit undefined, and a supplied instance fill the option", () => {
    const src =
      POINT +
      "export function g(a: number, p: Pt = new Pt(1)): number { return a + p.x; }\n" +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { h(a) >= 0 } */\n" +
      "export function h(a: number): number {\n" +
      "  return g(a) + g(a, undefined) + g(a, new Pt(a));\n}\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const h = emission.declarations[2];
    assert(h?.kind === "function");
    const ret = h.body[0];
    assert(ret?.kind === "return");
    const calls: EmitExpr[] = [];
    const collect = (e: EmitExpr) => {
      if (e.kind === "binop") {
        collect(e.left);
        collect(e.right);
      } else calls.push(e);
    };
    collect(ret.expr);
    expect(calls.map((c) => c.kind === "call" && c.args[1])).toEqual([
      { kind: "option" },
      { kind: "option" },
      {
        kind: "option",
        expr: {
          kind: "new",
          className: "Pt",
          args: [{ kind: "id", name: "a" }],
        },
      },
    ]);
  });

  test("a default constructing the enclosing class travels the source-order refusal", () => {
    // A member body cannot construct its own class either: the class is
    // not registered until its walk ends. The default takes the same road.
    const src = `export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 4)) { new Pt(a).plus() >= 0 } */
  plus(o: Pt = new Pt(1)): number {
    return this.x + o.x;
  }
}
`;
    expect(classifications(src).classified).toEqual([
      [
        "Error",
        "'Pt#plus' could not be modeled: parameter 'o' has a default the " +
          "model cannot evaluate: no model registered for 'Pt'",
      ],
    ]);
  });

  test("a constructor's instance default marks the binder tree", () => {
    const src =
      POINT +
      `export class Seg {
  readonly a: number;
  readonly b: number;
  constructor(a: Pt, b: Pt = new Pt(0)) {
    this.a = a.x;
    this.b = b.x;
  }
}
/** @ensures{p} forall (s: Seg) { len(s) >= 0 } */
export function len(s: Seg): number {
  return s.b - s.a;
}
`;
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.binders[0]).toMatchObject({
      ctorParams: [
        { name: "a", kind: "class", className: "Pt" },
        { name: "b", kind: "class", className: "Pt", defaulted: true },
      ],
    });
  });
});

describe("a body opens by resolving each default", () => {
  const ADD =
    "/** @ensures{p} forall (a: int ∈ [0, 5)) { add(a, a) >= 0 } */\n" +
    "export function add(x: number, y: number = 0): number {\n" +
    "  return x + y;\n}\n";

  test("a defaulted number is rebound at number ahead of the body", () => {
    const { emission } = emitModule(ADD, "t.ts");
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.body).toEqual([
      {
        kind: "const",
        name: "y",
        init: {
          kind: "cond",
          cond: {
            kind: "jsval-eq",
            semantics: "strict",
            left: { kind: "id", name: "y" },
            right: { kind: "inject", tag: "undefined" },
          },
          then: { kind: "num", lit: "0" },
          else: {
            kind: "project",
            tag: "number",
            expr: { kind: "id", name: "y" },
          },
        },
      },
      {
        kind: "return",
        expr: {
          kind: "binop",
          op: "+",
          left: { kind: "id", name: "x" },
          right: { kind: "id", name: "y" },
        },
      },
    ]);
  });

  test("a defaulted union rebinds at its declared union", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 } */\n" +
      "export function f(x: number, y: number | null | undefined = null): number {\n" +
      "  return x;\n}\n";
    const { emission } = emitModule(src, "t.ts");
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.body[0]).toEqual({
      kind: "const",
      name: "y",
      type: ["number", "undefined", "null"],
      init: {
        kind: "cond",
        cond: {
          kind: "jsval-eq",
          semantics: "strict",
          left: { kind: "id", name: "y" },
          right: { kind: "inject", tag: "undefined" },
        },
        then: { kind: "inject", tag: "null" },
        else: { kind: "id", name: "y" },
      },
    });
  });

  test("a parameter the body assigns opens as a mutable binding", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 } */\n" +
      "export function f(x: number, y: number = 1): number {\n" +
      "  y = y + x;\n  return y;\n}\n";
    const { emission } = emitModule(src, "t.ts");
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.body[0]).toMatchObject({ kind: "let", name: "y" });
  });

  test("an initializer sees earlier parameters at their declared type", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 } */\n" +
      "export function f(x: number, y: number = x * 2): number {\n" +
      "  return y;\n}\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.body[0]).toMatchObject({
      init: {
        then: {
          kind: "binop",
          op: "*",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "2" },
        },
      },
    });
  });

  test("an initializer naming a later parameter is the unbound invariant", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 } */\n" +
      "export function f(x: number = y, y: number = 1): number {\n" +
      "  return x;\n}\n";
    expect(classifications(src).classified).toEqual([
      [
        "Error",
        "'f' could not be modeled: parameter 'x' has a default the model " +
          "cannot evaluate: unbound identifier 'y'",
      ],
    ]);
  });

  test("an initializer outside the slice records its construct at a site", () => {
    const src =
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 } */\n" +
      "export function f(x: number, y: number = 2 ** 3): number {\n" +
      "  return x;\n}\n";
    expect(residualConstructs(src)).toEqual([
      "parameter 'y' has a default the model cannot evaluate: " +
        "'**' is not supported",
    ]);
  });

  test("an initializer calling into the model lowers as a call", () => {
    const src =
      "export function two(): number { return 2; }\n" +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 } */\n" +
      "export function f(x: number, y: number = two()): number {\n" +
      "  return x + y;\n}\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fn.body[0]).toMatchObject({
      init: { then: { kind: "call", callee: "two", args: [] } },
    });
  });
});

describe("class-typed parameters", () => {
  const gapSrc = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new Point(a).gap(new Point(a)) } */
  gap(other: Point): number {
    return other.x - this.x;
  }
}
`;

  test("models a method taking its own class, and the atom over it", () => {
    const { emission, classified } = emitModule(gapSrc, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods[0]!.params).toEqual([
      { name: "other", type: { class: "Point" } },
    ]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("a class-typed parameter is a receiver inside the method body", () => {
    const { emission } = emitModule(gapSrc, "t.ts");
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods[0]!.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "binop",
        op: "-",
        left: {
          kind: "field-read",
          className: "Point",
          field: "x",
          object: { kind: "id", name: "other" },
        },
        right: {
          kind: "field-read",
          className: "Point",
          field: "x",
          object: { kind: "self" },
        },
      },
    });
  });

  test("models a constructor taking an earlier class without degrading it", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
export class Wrap {
  readonly x: number;
  constructor(p: Point) {
    this.x = p.x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new Wrap(new Point(a)).v } */
  get v(): number {
    return this.x;
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const wrap = emission.declarations[1] as EmitClass;
    expect(wrap.ctor.params).toEqual([{ name: "p", type: { class: "Point" } }]);
    expect(wrap.ctor.body).toEqual([
      {
        kind: "field-set",
        field: "x",
        expr: {
          kind: "field-read",
          className: "Point",
          field: "x",
          object: { kind: "id", name: "p" },
        },
      },
    ]);
  });

  test("models a free function taking a class", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= gap(new Point(a)) } */
export function gap(p: Point): number {
  return p.x;
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[1] as EmitFunction;
    expect(fn.params).toEqual([{ name: "p", type: { class: "Point" } }]);
    expect(fn.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "field-read",
        className: "Point",
        field: "x",
        object: { kind: "id", name: "p" },
      },
    });
  });

  test("types a method call through a class-typed receiver", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  gap(other: Point): number {
    return other.x - this.x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new Point(a).twice(new Point(a)) } */
  twice(other: Point): number {
    return other.gap(other) + this.gap(other);
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods[1]!.body[0]).toMatchObject({
      kind: "return",
      expr: {
        kind: "binop",
        op: "+",
        left: {
          kind: "method-call",
          className: "Point",
          name: "gap",
          object: { kind: "id", name: "other" },
          args: [{ kind: "id", name: "other" }],
        },
        right: {
          kind: "method-call",
          className: "Point",
          name: "gap",
          object: { kind: "self" },
          args: [{ kind: "id", name: "other" }],
        },
      },
    });
  });

  test("refuses a later-declared class as a parameter type, member alone", () => {
    const src = `
export class A {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new A(a).m(a) } */
  m(b: B): number {
    return b.x;
  }
}
export class B {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /unmapped TypeScript construct 'TypeReference'/,
    );
  });

  test("travels a degraded class named as a parameter type", () => {
    const src = `
export abstract class Bad {}
export class A {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new A(a).m(a) } */
  m(b: Bad): number {
    return 1;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toMatch(/'Bad' could not be modeled/);
  });

  test("refuses a constructor parameter typed at its own class", () => {
    // The class is not modeled while its own constructor walks, so the
    // direct cycle refuses — and the constructor is the model's spine.
    const src = `
export class Node {
  readonly x: number;
  constructor(n: Node) {
    this.x = 1;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= a } */
  get v(): number {
    return this.x;
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(emission.declarations).toEqual([]);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /'Node#v' could not be modeled: unmapped TypeScript construct 'TypeReference'/,
    );
  });

  test("rejects a number where an instance is expected", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  gap(other: Point): number {
    return other.x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new Point(a).gap(a) } */
  get v(): number {
    return this.x;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /is a number, not an instance of 'Point'/,
    );
  });

  test("rejects an instance where a number is expected", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new Point(a).gap(new Point(a)) } */
  gap(other: Point): number {
    return other;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /identifier 'other' is an instance of 'Point', not a number/,
    );
  });

  test("rejects an instance of the wrong class", () => {
    const src = `
export class Q {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  gap(other: Point): number {
    return other.x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new Point(a).gap(new Q(a)) } */
  get v(): number {
    return this.x;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toMatch(
      /yields an instance of 'Q', not an instance of 'Point'/,
    );
  });

  test("binds an unannotated instance-valued local at its class", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= f(a) } */
export function f(a: number): number {
  const p = new Point(a);
  return a;
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toMatchObject({
      kind: "const",
      name: "p",
      type: { class: "Point" },
    });
  });

  test("a class-typed parameter shadows the builtin namespace it spells", () => {
    const src = `
export class Math {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  sqrt(): number {
    return this.x;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= f(new Math(a)) } */
export function f(Math: Math): number {
  return Math.sqrt();
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[1] as EmitFunction;
    expect(fn.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "method-call",
        className: "Math",
        name: "sqrt",
        object: { kind: "id", name: "Math" },
        args: [],
      },
    });
  });

  /** A Point with one extra member, and a free function over it. */
  function pointWith(member: string, body: string): string {
    return `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
${member}
}
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= f(new Point(a)) } */
export function f(p: Point): number {
${body}
}
`;
  }

  test("a private member of a class-typed parameter has no model", () => {
    expect(residualConstructs(pointWith("", "  return p.#x;"))).toEqual([
      expect.stringMatching(
        /unmapped TypeScript construct 'PropertyAccessExpression'/,
      ),
    ]);
  });

  test("a member read on a class-typed parameter is numeric-shaped", () => {
    const src = pointWith(
      "",
      "  if (Object.is(p.x, 0)) {\n    return 1;\n  }\n  return 0;",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[1] as EmitFunction;
    expect(fn.body[0]).toMatchObject({
      kind: "if",
      cond: {
        kind: "same-value",
        left: { kind: "field-read", field: "x", object: { kind: "id" } },
      },
    });
  });

  test("an opaque construct in a receiver call's argument degrades", () => {
    const src = pointWith(
      "  near(other: Point): number {\n    return other.x;\n  }",
      "  return p.near([0]);",
    );
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(
        /unmapped TypeScript construct 'ArrayLiteralExpression'/,
      ),
    ]);
  });

  test("a degraded method called on a class-typed parameter travels", () => {
    const src = pointWith(
      "  loops(): number {\n    for (;;) {}\n    return 1;\n  }",
      "  return p.loops();",
    );
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(
        /'Point#loops' could not be modeled: unmapped TypeScript construct 'ForStatement'/,
      ),
    ]);
  });

  test("a degraded getter read off a class-typed parameter travels", () => {
    const src = pointWith(
      "  get bad(): number {\n    for (;;) {}\n    return 1;\n  }",
      "  return p.bad;",
    );
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(
        /'Point#bad' could not be modeled: unmapped TypeScript construct 'ForStatement'/,
      ),
    ]);
  });

  test("a degraded member inside a receiver call's argument travels", () => {
    const src = pointWith(
      "  loops(): number {\n    for (;;) {}\n    return 1;\n  }\n" +
        "  near(other: Point): number {\n    return other.x;\n  }",
      "  return p.near(new Point(p.loops()));",
    );
    expect(residualConstructs(src)).toEqual([
      expect.stringMatching(/'Point#loops' could not be modeled/),
    ]);
  });

  test("an unknown method on a class-typed parameter is the engine's error", () => {
    const { classified } = emitModule(
      pointWith("", "  return p.nope();"),
      "t.ts",
    );
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /'Point' has no method 'nope' in the model/,
    );
  });

  test("a receiver method call checks its arity", () => {
    const src = pointWith(
      "  near(other: Point): number {\n    return other.x;\n  }",
      "  return p.near();",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /'Point#near' expects 1 argument\(s\), got 0/,
    );
  });

  test("a getter read off a class-typed parameter dispatches to the getter", () => {
    const src = pointWith(
      "  get v(): number {\n    return this.x;\n  }",
      "  return p.v;",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[1] as EmitFunction;
    expect(fn.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "getter-read",
        className: "Point",
        name: "v",
        object: { kind: "id", name: "p" },
      },
    });
  });

  test("a construction in an instance position checks the constructor's arity", () => {
    const src = pointWith(
      "  near(other: Point): number {\n    return other.x;\n  }",
      "  return p.near(new Point());",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /'Point' expects 1 argument\(s\), got 0/,
    );
  });

  test("refuses a parameter type no declaration binds", () => {
    const src = `
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= f(a) } */
export function f(p: Missing): number {
  return 1;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /unmapped TypeScript construct 'TypeReference'/,
    );
  });

  test("the reported method repro models", () => {
    const src = `export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: number) { 0 <= new Point(a).gap(new Point(a)) } */
  gap(other: Point): number {
    return other.x - this.x;
  }
}
`;
    const { emission, classified } = emitModule(src, "Gap.mts");
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("the reported constructor repro keeps the source-order refusal", () => {
    // Wrap's constructor names Point before Point has modeled, which is
    // the discipline every callee resolution follows.
    const src = `export class Wrap {
  readonly x: number;
  constructor(p: Point) {
    this.x = p.x;
  }
  /** @ensures{p} forall (a: number) { 0 <= a } */
  get v(): number {
    return this.x;
  }
}
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
`;
    const { classified } = emitModule(src, "Ctor.mts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toBe(
      "'Wrap#v' could not be modeled: unmapped TypeScript construct " +
        "'TypeReference' at 3:18",
    );
  });

  test("a reassigned class-typed parameter types its right-hand side", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
/** @ensures{reads} forall (a: int ∈ [0, 10)) { Object.is(reset(new Point(a)), 0) } */
export function reset(p: Point): number {
  p = new Point(0);
  return p.x;
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const fn = emission.declarations[1] as EmitFunction;
    expect(fn.body[0]).toEqual({
      kind: "assign",
      name: "p",
      expr: {
        kind: "new",
        className: "Point",
        args: [{ kind: "num", lit: "0" }],
      },
    });
  });

  test("a number cannot be assigned to a class-typed parameter", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
/** @ensures{reads} forall (a: int ∈ [0, 10)) { 0 <= reset(new Point(a)) } */
export function reset(p: Point): number {
  p = 1;
  return 0;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toMatch(
      /a numeric literal cannot be an instance of 'Point'/,
    );
  });

  test("refuses a generic instantiation as a parameter type", () => {
    const src = `
export class Point<T> {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= f(a) } */
export function f(p: Point<number>): number {
  return 1;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /unmapped TypeScript construct 'TypeReference'/,
    );
  });

  test("travels a declaration that failed without naming a construct", () => {
    const src = `
export function bad(x: number): number {
  return y;
}
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= f(a) } */
export function f(p: bad): number {
  return 1;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /'bad' could not be modeled: unbound identifier 'y'/,
    );
  });

  test("an unknown member of a class-typed parameter is the engine's error", () => {
    const src = `
export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= f(new Point(a)) } */
export function f(p: Point): number {
  return p.y;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /'Point' has no member 'y' in the model/,
    );
  });
});

describe("module-level const bindings", () => {
  test("an initializer admits a whitelisted builtin call over constants", () => {
    const src = [
      "const root2 = Math.sqrt(2);",
      "/** @ensures{p} forall (n: int ∈ [0, 10)) { diagonal(n) >= 0 } */",
      "export function diagonal(x: number): number {",
      "  return x * root2;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "init-call.ts");
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.declarations[0]).toEqual({
      kind: "constant",
      name: "root2",
      init: {
        kind: "builtin",
        object: "Math",
        member: "sqrt",
        args: [{ kind: "num", lit: "2" }],
      },
      source: "const root2 = Math.sqrt(2);",
    });
    expect(fnBody(emission.declarations[1]!)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "binop",
          op: "*",
          left: { kind: "id", name: "x" },
          right: { kind: "const-read", name: "root2" },
        },
      },
    ]);
  });

  test.each([
    ["Infinity", { kind: "num", lit: "Infinity" }],
    ["NaN", { kind: "num", lit: "NaN" }],
    [
      "-Infinity",
      { kind: "unop", op: "-", operand: { kind: "num", lit: "Infinity" } },
    ],
  ])("an initializer admits the global atom %s", (spelling, init) => {
    const src = [
      `const limit = ${spelling};`,
      "/** @ensures{p} forall (n: int ∈ [0, 10)) { shrink(n) >= 0 } */",
      "export function shrink(x: number): number {",
      "  return x / limit;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "init-atom.ts");
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({ kind: "constant", name: "limit", init }),
    );
  });

  test("an initializer admits a builtin constant read", () => {
    const src = [
      "const EPSILON = Number.EPSILON;",
      "/** @ensures{p} forall (n: int ∈ [0, 10)) { nudge(n) >= 0 } */",
      "export function nudge(x: number): number {",
      "  return x + EPSILON;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "init-read.ts");
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({
        kind: "constant",
        name: "EPSILON",
        init: { kind: "builtin-read", object: "Number", member: "EPSILON" },
      }),
    );
  });

  test("the new shapes compose with arithmetic and each other", () => {
    const src = [
      "const twoPi = 2 * Math.PI;",
      "const tiny = Math.abs(-Number.EPSILON);",
      "const lo = Math.min(twoPi, tiny, 1);",
      "/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */",
      "export function f(x: number): number {",
      "  return x * lo;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "init-compose.ts");
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    expect(emission.declarations.slice(0, 3)).toEqual([
      expect.objectContaining({
        name: "twoPi",
        init: {
          kind: "binop",
          op: "*",
          left: { kind: "num", lit: "2" },
          right: { kind: "builtin-read", object: "Math", member: "PI" },
        },
      }),
      expect.objectContaining({
        name: "tiny",
        init: {
          kind: "builtin",
          object: "Math",
          member: "abs",
          args: [
            {
              kind: "unop",
              op: "-",
              operand: {
                kind: "builtin-read",
                object: "Number",
                member: "EPSILON",
              },
            },
          ],
        },
      }),
      expect.objectContaining({
        name: "lo",
        init: {
          kind: "builtin",
          object: "Math",
          member: "min",
          args: [
            { kind: "const-read", name: "twoPi" },
            { kind: "const-read", name: "tiny" },
            { kind: "num", lit: "1" },
          ],
        },
      }),
    ]);
  });

  test("a formula atom reads a constant initialized from a builtin", () => {
    const src = [
      "const root2 = Math.sqrt(2);",
      "/** @ensures{p} forall (n: int ∈ [0, 10)) { keep(n) <= root2 } */",
      "export function keep(x: number): number {",
      "  return 0;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "init-atom-read.ts");
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toEqual(
      expect.objectContaining({
        expr: expect.objectContaining({
          right: { kind: "const-read", name: "root2" },
        }),
      }),
    );
  });

  test("a module binding of an atom spelling is read as that binding", () => {
    const src = [
      "const Infinity = 5;",
      "const limit = Infinity;",
      "/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */",
      "export function f(x: number): number {",
      "  return x * limit;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "shadow-atom.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[1]).toEqual(
      expect.objectContaining({
        name: "limit",
        init: { kind: "const-read", name: "Infinity" },
      }),
    );
  });

  test("a module binding of the namespace spelling declines the initializer call", () => {
    const src = [
      "const Math = null;",
      "const root2 = Math.sqrt(2);",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n * root2;",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "shadowed-init.ts")).toEqual([
      expect.stringContaining(
        "'root2' could not be modeled: unmapped TypeScript construct " +
          "'VariableStatement'",
      ),
    ]);
  });

  test("an unresolved import of the namespace spelling declines the initializer read", () => {
    const src = [
      'import { Number } from "./nowhere.js";',
      "const EPSILON = Number.EPSILON;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n + EPSILON;",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "shadowed-import-init.ts")).toEqual([
      expect.stringContaining(
        "'EPSILON' could not be modeled: unmapped TypeScript construct " +
          "'VariableStatement'",
      ),
    ]);
  });

  test("a call member spelling in an initializer still registers as an alias", () => {
    const src = [
      "const safeSqrt = Math.sqrt;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return safeSqrt(n);",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "alias-still.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations).toHaveLength(1);
    expect(fnBody(emission.declarations[0]!)).toEqual([
      {
        kind: "return",
        expr: {
          kind: "builtin",
          object: "Math",
          member: "sqrt",
          args: [{ kind: "id", name: "n" }],
        },
      },
    ]);
  });

  test.each([
    ["const b = Number.isNaN(1);", "b"],
    ["const r = Math.sqrt();", "r"],
    ["const l = Math.log(2);", "l"],
    ["const len = Number.length;", "len"],
    ["const m = Math.sqrt(twoPi);", "m"],
  ])(
    "an initializer outside the slice keeps its degradation: %s",
    (decl, name) => {
      const src = [
        decl,
        `/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */`,
        "export function f(n: number): number {",
        `  return n * ${name};`,
        "}",
        "",
      ].join("\n");
      expect(residualConstructs(src, "init-declines.ts")).toEqual([
        expect.stringContaining(
          `'${name}' could not be modeled: unmapped TypeScript construct 'VariableStatement'`,
        ),
      ]);
    },
  );

  test("a formula atom reads an admitted constant", () => {
    const src = [
      "const cap = 100;",
      "/** @ensures{bounded} forall (n: int ∈ [0, 10)) { keep(n) <= cap } */",
      "export function keep(n: number): number {",
      "  return n;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "formula-const.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.conclusion).toEqual({
      kind: "istrue",
      expr: {
        kind: "binop",
        op: "<=",
        left: {
          kind: "call",
          callee: "keep",
          args: [{ kind: "id", name: "n" }],
        },
        right: { kind: "const-read", name: "cap" },
      },
    });
  });

  test("a call through a builtin alias lowers as the builtin", () => {
    const src = [
      "const safeMathAbs = Math.abs;",
      "/** @ensures{nonNegative} forall (n: int ∈ [-10, 10)) { magnitude(n) >= 0 } */",
      "export function magnitude(n: number): number {",
      "  return safeMathAbs(n);",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "alias-const.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        kind: "function",
        name: "magnitude",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "abs",
              args: [{ kind: "id", name: "n" }],
            },
          },
        ],
      }),
    ]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("a boolean-valued builtin alias works in guard position", () => {
    const src = [
      "const finite = Number.isFinite;",
      "/** @ensures{id} forall (x: number) { finite(x) -> keep(x) ≡ x } */",
      "export function keep(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "alias-guard.ts");
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.guards).toEqual([
      {
        kind: "builtin",
        object: "Number",
        member: "isFinite",
        args: [{ kind: "id", name: "x" }],
      },
    ]);
  });

  test("a module-scope let stays degraded and its read travels the refusal", () => {
    const src = [
      "let factor = 2;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n * factor;",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "let.ts")).toEqual([
      "'factor' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement' at 1:5",
    ]);
  });

  test("a non-literal initializer keeps the declarator degraded", () => {
    const src = [
      "const label = 'ms';",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n + label;",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "string.ts")).toEqual([
      expect.stringContaining(
        "'label' could not be modeled: unmapped TypeScript construct " +
          "'VariableStatement'",
      ),
    ]);
  });

  test("a number type annotation admits; any other declines", () => {
    const src = [
      "const wide: number = 3;",
      "const narrow: 3 = 3;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n + wide + narrow;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "annotated.ts");
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({
        kind: "constant",
        name: "wide",
        init: { kind: "num", lit: "3" },
      }),
    );
    expect(residualConstructs(src, "annotated.ts")).toEqual([
      expect.stringContaining("'narrow' could not be modeled"),
    ]);
  });

  test("a negated literal initializer models with its sign", () => {
    const src = [
      "const floor = -5;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= floor } */",
      "export function f(n: number): number {",
      "  return n;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "negated.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({
        kind: "constant",
        name: "floor",
        init: { kind: "num", lit: "-5" },
      }),
    );
  });

  test("a declarator mixing admitted and degraded siblings contains the damage", () => {
    const src = [
      "const s = 1000, m = minutes();",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n * s;",
      "}",
      "/** @ensures{q} forall (n: int ∈ [0, 4)) { g(n) >= 0 } */",
      "export function g(n: number): number {",
      "  return n * m;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "mixed.ts");
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({
        kind: "constant",
        name: "s",
        init: { kind: "num", lit: "1000" },
      }),
    );
    expect(residualConstructs(src, "mixed.ts")).toEqual([
      expect.stringContaining("'m' could not be modeled"),
    ]);
  });

  test("a parameter or local shadows a module constant", () => {
    const src = [
      "const cap = 100;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n, n) >= 0 } */",
      "export function f(n: number, cap: number): number {",
      "  return n + cap;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "shadow.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[1]!)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "binop",
        op: "+",
        left: { kind: "id", name: "n" },
        right: { kind: "id", name: "cap" },
      },
    });
  });

  test("a value-position read of a builtin alias is refused, not the engine's error", () => {
    const src = [
      "const safeMathAbs = Math.abs;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return safeMathAbs;",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "alias-value.ts")).toEqual([
      expect.stringContaining(
        "'safeMathAbs' aliases 'Math.abs', which is modeled only as a callee",
      ),
    ]);
  });

  test("an alias call with the wrong arity mirrors the direct spelling's refusal", () => {
    const src = [
      "const safeMathAbs = Math.abs;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return safeMathAbs(n, n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "alias-arity.ts")).toEqual([
      "'Math.abs' takes one argument",
    ]);
  });

  test("a variadic builtin's alias admits every arity", () => {
    const src = [
      "const smallest = Math.min;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) <= 0 } */",
      "export function f(n: number): number {",
      "  return smallest(n, 0, -n);",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "alias-variadic.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations).toEqual([
      expect.objectContaining({
        kind: "function",
        name: "f",
        body: [
          {
            kind: "return",
            expr: {
              kind: "builtin",
              object: "Math",
              member: "min",
              args: [
                { kind: "id", name: "n" },
                { kind: "num", lit: "0" },
                { kind: "unop", op: "-", operand: { kind: "id", name: "n" } },
              ],
            },
          },
        ],
      }),
    ]);
  });

  test("a module binding of the namespace spelling declines the alias", () => {
    const src = [
      "const Math = null;",
      "const safeMathAbs = Math.abs;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return safeMathAbs(n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "shadowed-ns.ts")).toEqual([
      expect.stringContaining(
        "'safeMathAbs' could not be modeled: unmapped TypeScript construct " +
          "'VariableStatement'",
      ),
    ]);
  });

  test("an alias of an unlisted builtin member stays degraded", () => {
    const src = [
      "const safeMathPow = Math.pow;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return safeMathPow(n, n);",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "unlisted.ts")).toEqual([
      expect.stringContaining(
        "'safeMathPow' could not be modeled: unmapped TypeScript construct " +
          "'VariableStatement'",
      ),
    ]);
  });

  test("calling a literal constant is refused by name", () => {
    const src = [
      "const cap = 100;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return cap(n);",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "call-const.ts");
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Error",
        reason: expect.stringContaining(
          "'cap' is a constant; it cannot be called",
        ),
      }),
    ]);
  });

  test("a declare const stays degraded", () => {
    const src = [
      "declare const ambient = 5;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n + ambient;",
      "}",
      "",
    ].join("\n");
    expect(residualConstructs(src, "ambient.ts")).toEqual([
      expect.stringContaining(
        "'ambient' could not be modeled: unmapped TypeScript construct " +
          "'VariableStatement'",
      ),
    ]);
  });

  test("a formula atom reading a degraded const travels its refusal", () => {
    const src = [
      "const cap = limit();",
      "/** @ensures{bounded} forall (n: int ∈ [0, 10)) { keep(n) <= cap } */",
      "export function keep(n: number): number {",
      "  return n;",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(src, "formula-const.ts");
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason:
          "'cap' could not be modeled: unmapped TypeScript construct " +
          "'VariableStatement' at 1:7",
      }),
    ]);
  });

  test("a literal const models and a body read references it", () => {
    const src = [
      "const millisecondsInSecond = 1000;",
      "/** @ensures{nonNegative} forall (s: int ∈ [0, 10)) { secondsToMilliseconds(s) >= 0 } */",
      "export function secondsToMilliseconds(seconds: number): number {",
      "  return seconds * millisecondsInSecond;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "module-const.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations).toEqual([
      {
        kind: "constant",
        name: "millisecondsInSecond",
        init: { kind: "num", lit: "1000" },
        source: "const millisecondsInSecond = 1000;",
      },
      {
        kind: "function",
        name: "secondsToMilliseconds",
        params: [{ name: "seconds", type: "number" }],
        source: expect.stringContaining(
          "export function secondsToMilliseconds",
        ),
        body: [
          {
            kind: "return",
            expr: {
              kind: "binop",
              op: "*",
              left: { kind: "id", name: "seconds" },
              right: { kind: "const-read", name: "millisecondsInSecond" },
            },
          },
        ],
      },
    ]);
    expect(emission.obligations).toHaveLength(1);
    expectValidEmission(emission);
  });

  test("a constant derived from earlier constants models with its derivation", () => {
    const src = [
      "const s = 1000;",
      "const m = s * 60;",
      "const h = m * 60 + -s;",
      "/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { toMinutes(x) >= 0 } */",
      "export function toMinutes(x: number): number {",
      "  return x * m;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "ladder.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations.slice(0, 3)).toEqual([
      {
        kind: "constant",
        name: "s",
        init: { kind: "num", lit: "1000" },
        source: "const s = 1000;",
      },
      {
        kind: "constant",
        name: "m",
        init: {
          kind: "binop",
          op: "*",
          left: { kind: "const-read", name: "s" },
          right: { kind: "num", lit: "60" },
        },
        source: "const m = s * 60;",
      },
      {
        kind: "constant",
        name: "h",
        init: {
          kind: "binop",
          op: "+",
          left: {
            kind: "binop",
            op: "*",
            left: { kind: "const-read", name: "m" },
            right: { kind: "num", lit: "60" },
          },
          right: {
            kind: "unop",
            op: "-",
            operand: { kind: "const-read", name: "s" },
          },
        },
        source: "const h = m * 60 + -s;",
      },
    ]);
    expect(fnBody(emission.declarations[3]!)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "binop",
        op: "*",
        left: { kind: "id", name: "x" },
        right: { kind: "const-read", name: "m" },
      },
    });
    expectValidEmission(emission);
  });

  test("an initializer admits division, remainder, unary plus, and parentheses", () => {
    const src = [
      "const m = 60000;",
      "const q = +(m / 7) % 2;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n + q;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "ops.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[1]).toEqual({
      kind: "constant",
      name: "q",
      init: {
        kind: "binop",
        op: "%",
        left: {
          kind: "unop",
          op: "+",
          operand: {
            kind: "binop",
            op: "/",
            left: { kind: "const-read", name: "m" },
            right: { kind: "num", lit: "7" },
          },
        },
        right: { kind: "num", lit: "2" },
      },
      source: "const q = +(m / 7) % 2;",
    });
    expectValidEmission(emission);
  });

  test("declarators in one statement admit in order", () => {
    const src = [
      "const s = 1000, m = s * 60;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n * m;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "list.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[1]).toEqual(
      expect.objectContaining({
        kind: "constant",
        name: "m",
        init: {
          kind: "binop",
          op: "*",
          left: { kind: "const-read", name: "s" },
          right: { kind: "num", lit: "60" },
        },
      }),
    );
  });

  test("a forward or self reference is not yet admitted and degrades", () => {
    const src = [
      "const m = s * 60;",
      "const s = 1000;",
      "const t = t + 1;",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n * m;",
      "}",
      "/** @ensures{q} forall (n: int ∈ [0, 4)) { g(n) >= 0 } */",
      "export function g(n: number): number {",
      "  return n * t;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "forward.ts");
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({ kind: "constant", name: "s" }),
    );
    expect(residualConstructs(src, "forward.ts")).toEqual([
      "'m' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement' at 1:7",
      "'t' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement' at 3:7",
    ]);
  });

  test("a call, a boolean builtin, an unsupported operator, or a mutable read keeps the degradation", () => {
    const src = [
      "let base = 2;",
      "const a = base * 3;",
      "const b = Number.isNaN(3);",
      "const c = 2 ** 3;",
      "const d = minutes();",
      "const e = 1 < 2;",
      "function minutes(): number { return 1; }",
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { f(n) >= 0 } */",
      "export function f(n: number): number {",
      "  return n + a + b + c + d + e;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "declines.ts");
    expect(emission.declarations.filter((d) => d.kind === "constant")).toEqual(
      [],
    );
    expect(residualConstructs(src, "declines.ts")[0]).toBe(
      "'a' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement' at 2:7",
    );
  });
});

describe("union-typed parameters", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("a keyword union maps as a normalized tag array", () => {
    const { emission } = emit(
      `export function f(v: string | number, w: null | undefined | number): number {\n  return 0;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn !== undefined && fn.kind === "function");
    expect(fn.params).toEqual([
      { name: "v", type: ["number", "string"] },
      { name: "w", type: ["number", "undefined", "null"] },
    ]);
  });

  test("duplicate tags deduplicate; a one-tag union of number is num", () => {
    const { emission } = emit(
      `export function f(v: number | number): number {\n  return v;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn !== undefined && fn.kind === "function");
    expect(fn.params).toEqual([{ name: "v", type: "number" }]);
  });

  test("a non-keyword member refuses the whole parameter", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), x) } */\n` +
        `export function f(v: number | "a"): number {\n  return 0;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'LiteralType' at 2:31",
      ],
    ]);
  });

  test("a constructor keeps the union ban", () => {
    const src =
      `export class C {\n  v: number;\n  constructor(v: number | string) {\n    this.v = 0;\n  }\n}\n` +
      `/** @ensures{p} forall (x: number) { Object.is(get(x), x) } */\n` +
      `export function get(x: number): number {\n  return new C(x).v;\n}\n`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'UnionType'"),
    ]);
  });

  test("a number argument injects at a union slot; a union identifier projects at a number position", () => {
    const { emission } = emit(
      `export function toNum(v: number | string): number {\n  return v;\n}\n` +
        `export function call(x: number): number {\n  return toNum(x + 1);\n}\n`,
    );
    const [toNum, call] = emission.declarations;
    assert(toNum?.kind === "function" && call?.kind === "function");
    expect(toNum.body).toEqual([
      {
        kind: "return",
        expr: {
          kind: "project",
          tag: "number",
          expr: { kind: "id", name: "v" },
        },
      },
    ]);
    expect(call.body).toEqual([
      {
        kind: "return",
        expr: {
          kind: "call",
          callee: "toNum",
          args: [
            {
              kind: "inject",
              tag: "number",
              expr: {
                kind: "binop",
                op: "+",
                left: { kind: "id", name: "x" },
                right: { kind: "num", lit: "1" },
              },
            },
          ],
        },
      },
    ]);
  });

  test("undefined and null inject where the union carries their tag", () => {
    const { emission } = emit(
      `export function opt(v: number | null | undefined): number {\n  return 0;\n}\n` +
        `export function call(): number {\n  return opt(null) + opt(undefined);\n}\n`,
    );
    const call = emission.declarations[1];
    assert(call?.kind === "function");
    expect(fnBody(call)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "binop",
        op: "+",
        left: {
          kind: "call",
          callee: "opt",
          args: [{ kind: "inject", tag: "null" }],
        },
        right: {
          kind: "call",
          callee: "opt",
          args: [{ kind: "inject", tag: "undefined" }],
        },
      },
    });
  });

  test("a binding of 'undefined' shadows the atom, like NaN's", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(call(x), 0) } */\n` +
        `export function opt(v: number | undefined): number {\n  return 0;\n}\n` +
        `export function call(undefined: number): number {\n  return opt(undefined);\n}\n`,
    );
    // Shadowed: the parameter is a number, so it injects at "number".
    expect(classified).toEqual([]);
  });

  test("identical unions flow un-wrapped; different unions refuse as the engine's error", () => {
    const relay = emit(
      `export function toNum(v: number | string): number {\n  return 0;\n}\n` +
        `/** @ensures{p} forall (x: number) { Object.is(relay(x), 0) } */\n` +
        `export function relay(v: number | string): number {\n  return toNum(v);\n}\n`,
    );
    const relayFn = relay.emission.declarations[1];
    assert(relayFn?.kind === "function");
    expect(fnBody(relayFn)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "call",
        callee: "toNum",
        args: [{ kind: "id", name: "v" }],
      },
    });

    const widened =
      `export function wide(v: number | string | boolean): number {\n  return 0;\n}\n` +
      `/** @ensures{p} forall (x: number) { Object.is(narrow(x), 0) } */\n` +
      `export function narrow(v: number | string): number {\n  return wide(v);\n}\n`;
    expect(residualConstructs(widened)).toEqual([
      "'v' is a 'number | string' value, not a 'number | string | boolean' " +
        "value; unions flow only between identical spellings",
    ]);
  });

  test("a union-valued return keeps its refusal", () => {
    const ret = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), x) } */\n` +
        `export function f(v: number | string): number | string {\n  return v;\n}\n`,
    );
    expect(ret.classified[0]?.szs).toBe("Inappropriate");
    expect(ret.classified[0]?.reason).toContain("'UnionType'");
  });

  test("null outside a union position keeps its construct refusal, reason intact", () => {
    const src =
      `/** @ensures{p} forall (x: number) { Object.is(f(x), x) } */\n` +
      `export function f(x: number): number {\n  return null;\n}\n`;
    expect(residualConstructs(src)).toEqual([
      "unmapped TypeScript construct 'NullKeyword' at 3:10",
    ]);
  });

  test("typeof dispatch lowers to a typeof test; !== negates it", () => {
    const { emission } = emit(
      `export function toNum(v: number | string): number {\n` +
        `  if (typeof v === "number") {\n    return v;\n  }\n  return 0;\n}\n` +
        `export function other(v: number | string): number {\n` +
        `  if ("number" !== typeof v) {\n    return 0;\n  }\n  return v;\n}\n`,
    );
    const [toNum, other] = emission.declarations;
    assert(toNum?.kind === "function" && other?.kind === "function");
    expect(fnBody(toNum)[0]).toEqual({
      kind: "if",
      cond: {
        kind: "typeof-test",
        expr: { kind: "id", name: "v" },
        result: "number",
      },
      then: [
        {
          kind: "return",
          expr: {
            kind: "project",
            tag: "number",
            expr: { kind: "id", name: "v" },
          },
        },
      ],
    });
    const first = fnBody(other)[0];
    assert(first?.kind === "if");
    expect(first.cond).toEqual({
      kind: "unop",
      op: "!",
      operand: {
        kind: "typeof-test",
        expr: { kind: "id", name: "v" },
        result: "number",
      },
    });
  });

  test("an unrecognized literal, a non-union operand, and typeof outside a comparison all degrade as the construct", () => {
    for (const body of [
      `if (typeof v === "numbr") {\n    return 0;\n  }\n  return 0;`,
      `const t = typeof v;\n  return 0;`,
    ]) {
      const src =
        `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(v: number | string): number {\n  ${body}\n}\n`;
      expect(residualConstructs(src)).toEqual([
        expect.stringContaining("'TypeOfExpression'"),
      ]);
    }
    const plain =
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
      `export function f(v: number): number {\n` +
      `  if (typeof v === "number") {\n    return v;\n  }\n  return 0;\n}\n`;
    expect(residualConstructs(plain)).toEqual([
      expect.stringContaining("'TypeOfExpression'"),
    ]);
  });

  test("=== with a union operand lowers to strictEq; Object.is to sameValue; !== negates", () => {
    const { emission } = emit(
      `export function f(v: number | null, w: number | null): number {\n` +
        `  if (v === null) {\n    return 1;\n  }\n` +
        `  if (Object.is(v, w)) {\n    return 2;\n  }\n` +
        `  if (v !== undefined) {\n    return 3;\n  }\n` +
        `  return 0;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    const [first, second, third] = fnBody(fn);
    assert(
      first?.kind === "if" && second?.kind === "if" && third?.kind === "if",
    );
    expect(first.cond).toEqual({
      kind: "jsval-eq",
      semantics: "strict",
      left: { kind: "id", name: "v" },
      right: { kind: "inject", tag: "null" },
    });
    expect(second.cond).toEqual({
      kind: "jsval-eq",
      semantics: "same-value",
      left: { kind: "id", name: "v" },
      right: { kind: "id", name: "w" },
    });
    expect(third.cond).toEqual({
      kind: "unop",
      op: "!",
      operand: {
        kind: "jsval-eq",
        semantics: "strict",
        left: { kind: "id", name: "v" },
        right: { kind: "inject", tag: "undefined" },
      },
    });
  });

  test("a boolean-valued side of a union equality injects at its tag (#209)", () => {
    const { emission, classified } = emit(
      `export function f(v: number | string, x: number): number {\n` +
        `  if (v === Number.isFinite(x)) {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    const first = fnBody(fn)[0];
    assert(first?.kind === "if");
    expect(first.cond).toEqual({
      kind: "jsval-eq",
      semantics: "strict",
      left: { kind: "id", name: "v" },
      right: {
        kind: "inject",
        tag: "boolean",
        expr: {
          kind: "builtin",
          object: "Number",
          member: "isFinite",
          args: [{ kind: "id", name: "x" }],
        },
      },
    });
  });

  test("the statically number side of a union equality injects", () => {
    const { emission } = emit(
      `export function f(v: number | string, x: number): number {\n` +
        `  if (v === x + 1) {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    const first = fnBody(fn)[0];
    assert(first?.kind === "if");
    expect(first.cond).toEqual({
      kind: "jsval-eq",
      semantics: "strict",
      left: { kind: "id", name: "v" },
      right: {
        kind: "inject",
        tag: "number",
        expr: {
          kind: "binop",
          op: "+",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "1" },
        },
      },
    });
  });

  test("a string literal against a union operand keeps its refusal", () => {
    const eq =
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
      `export function f(v: number | string): number {\n` +
      `  if (v === "a") {\n    return 1;\n  }\n  return 0;\n}\n`;
    expect(residualConstructs(eq)).toEqual([
      expect.stringContaining("'StringLiteral'"),
    ]);
    const same =
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
      `export function f(v: number | string): number {\n` +
      `  if (Object.is(v, "a")) {\n    return 1;\n  }\n  return 0;\n}\n`;
    expect(residualConstructs(same)).toEqual([
      "unmapped TypeScript construct 'StringLiteral' at 3:20",
    ]);
  });

  test("without a union operand, a string argument keeps the same refusal", () => {
    const src =
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
      `export function f(x: number): number {\n` +
      `  if (Object.is(x, "a")) {\n    return 1;\n  }\n  return 0;\n}\n`;
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        expect.stringContaining(
          "'Object.is' admits numbers, booleans, union values",
        ),
      ],
    ]);
  });

  test("bigint and boolean members carry their own tags", () => {
    const { emission } = emit(
      `export function f(v: boolean | bigint | number): number {\n  return 0;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn !== undefined && fn.kind === "function");
    expect(fn.params).toEqual([
      { name: "v", type: ["number", "bigint", "boolean"] },
    ]);
  });

  test("a typeof whose operand is not an identifier, or whose literal side is not a string, is not the shape", () => {
    const call =
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
      `export function id(v: number | string): number {\n  return 0;\n}\n` +
      `export function f(v: number | string): number {\n` +
      `  if (typeof id(v) === "number") {\n    return 1;\n  }\n  return 0;\n}\n`;
    expect(residualConstructs(call)).toEqual([
      expect.stringContaining("'TypeOfExpression'"),
    ]);

    const nonLiteral =
      `/** @ensures{p} forall (x: number) { Object.is(f(x, x), 0) } */\n` +
      `export function f(v: number | string, s: number): number {\n` +
      `  if (typeof v === s) {\n    return 1;\n  }\n  return 0;\n}\n`;
    expect(residualConstructs(nonLiteral)).toEqual([
      expect.stringContaining("'TypeOfExpression'"),
    ]);
  });

  test("a boolean-yielding union test refuses at a number position", () => {
    for (const [body, needle] of [
      [`return typeof v === "number";`, "a 'typeof' test yields a boolean"],
      [`return v === null;`, "operator '===' yields a boolean"],
      [`return Object.is(v, null);`, "a call to 'Object.is' yields a boolean"],
    ]) {
      const { classified } = emit(
        `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
          `export function f(v: number | null): number {\n  ${body}\n}\n`,
      );
      expect(classified[0]?.szs).toBe("Error");
      expect(classified[0]?.reason).toContain(needle!);
    }
  });

  test("an atom a union slot cannot hold refuses at the slot", () => {
    const nullArg =
      `/** @ensures{p} forall (x: number) { Object.is(call(x), 0) } */\n` +
      `export function toNum(v: number | string): number {\n  return 0;\n}\n` +
      `export function call(x: number): number {\n  return toNum(null);\n}\n`;
    expect(residualConstructs(nullArg)).toEqual([
      "unmapped TypeScript construct 'NullKeyword' at 6:16",
    ]);

    const numberArg = emit(
      `/** @ensures{p} forall (x: number) { Object.is(call(x), 0) } */\n` +
        `export function opt(v: string | undefined): number {\n  return 0;\n}\n` +
        `export function call(x: number): number {\n  return opt(x);\n}\n`,
    );
    expect(numberArg.classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "property elaboration failed: 'call' has no model: a 'string | undefined' " +
          "value slot has no 'number' member, so a number-valued expression " +
          "cannot flow to it",
      ],
    ]);
  });
});

describe("union-typed locals (#117)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("a union-annotated const rides the wire with its normalized tags", () => {
    const { emission, classified } = emit(
      `export function carry(v: number | string): number {\n` +
        `  const w: string | number = v;\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "w",
      init: { kind: "id", name: "v" },
      type: ["number", "string"],
    });
  });

  test("a number-valued initializer injects at the local's slot", () => {
    const { emission } = emit(
      `export function f(x: number): number {\n` +
        `  const w: number | undefined = x + 1;\n  return x;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "w",
      init: {
        kind: "inject",
        tag: "number",
        expr: {
          kind: "binop",
          op: "+",
          left: { kind: "id", name: "x" },
          right: { kind: "num", lit: "1" },
        },
      },
      type: ["number", "undefined"],
    });
  });

  test("undefined and null inject where the local's union carries their tag", () => {
    const { emission, classified } = emit(
      `export function f(x: number): number {\n` +
        `  const u: number | undefined = undefined;\n` +
        `  const n: number | null = null;\n  return x;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn).slice(0, 2)).toEqual([
      {
        kind: "const",
        name: "u",
        init: { kind: "inject", tag: "undefined" },
        type: ["number", "undefined"],
      },
      {
        kind: "const",
        name: "n",
        init: { kind: "inject", tag: "null" },
        type: ["number", "null"],
      },
    ]);
  });

  test("a union local reads back under a parameter's rules: typeof, tagged equality, projection", () => {
    const { emission, classified } = emit(
      `export function f(v: number | string): number {\n` +
        `  const w: number | string = v;\n` +
        `  if (typeof w === "string") {\n    return 0;\n  }\n` +
        `  if (w === 1) {\n    return 1;\n  }\n` +
        `  return w;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    const [, dispatch, eq, last] = fnBody(fn);
    assert(dispatch?.kind === "if" && eq?.kind === "if");
    expect(dispatch.cond).toEqual({
      kind: "typeof-test",
      expr: { kind: "id", name: "w" },
      result: "string",
    });
    expect(eq.cond).toEqual({
      kind: "jsval-eq",
      semantics: "strict",
      left: { kind: "id", name: "w" },
      right: { kind: "inject", tag: "number", expr: { kind: "num", lit: "1" } },
    });
    expect(last).toEqual({
      kind: "return",
      expr: { kind: "project", tag: "number", expr: { kind: "id", name: "w" } },
    });
  });

  test("a mutable union let reassigns at its declared type", () => {
    const { emission, classified } = emit(
      `export function f(x: number): number {\n` +
        `  let w: number | undefined = undefined;\n` +
        `  w = x;\n  return x;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn).slice(0, 2)).toEqual([
      {
        kind: "let",
        name: "w",
        init: { kind: "inject", tag: "undefined" },
        type: ["number", "undefined"],
      },
      {
        kind: "assign",
        name: "w",
        expr: {
          kind: "inject",
          tag: "number",
          expr: { kind: "id", name: "x" },
        },
      },
    ]);
  });

  test("mismatched union spellings refuse as the engine's error", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(v: number | boolean): number {\n` +
        `  const w: number | string = v;\n  return 0;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "'f' could not be modeled: 'v' is a 'number | boolean' value, " +
          "not a 'number | string' value; unions flow only between identical spellings",
      ],
    ]);
  });

  test("a one-tag union annotation is its base type, exactly as a parameter's", () => {
    const { emission } = emit(
      `export function f(x: number): number {\n` +
        `  const w: number | number = x;\n  return w;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "w",
      init: { kind: "id", name: "x" },
    });
  });

  test("a one-tag union of a non-number keyword keeps the statement refusal", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(x: number): number {\n` +
        `  const w: string | string = "a";\n  return 0;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'VariableStatement' at 3:3",
      ],
    ]);
  });

  test("a union with a non-keyword member keeps the statement refusal", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(x: number): number {\n` +
        `  const w: number | "a" = x;\n  return 0;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'VariableStatement' at 3:3",
      ],
    ]);
  });

  test("a lone non-number keyword keeps the statement refusal", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */\n` +
        `export function f(n: number): number {\n` +
        `  const label: string = "m";\n  return n;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'VariableStatement' at 3:3",
      ],
    ]);
  });
});

describe("class-typed locals (#117)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");
  const PT = `export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  twice(): number {
    return this.x * 2;
  }
}
`;

  test("a class-annotated const rides the wire at its class", () => {
    const { emission, classified } = emit(
      `${PT}export function f(q: Pt): number {\n` +
        `  const p: Pt = q;\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "p",
      init: { kind: "id", name: "q" },
      type: { class: "Pt" },
    });
  });

  test("a construction meets the local's class as a slot", () => {
    const { emission, classified } = emit(
      `${PT}export function f(n: number): number {\n` +
        `  const p: Pt = new Pt(n);\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "p",
      init: { kind: "new", className: "Pt", args: [{ kind: "id", name: "n" }] },
      type: { class: "Pt" },
    });
  });

  test("a field read on a class local is a place", () => {
    const { emission, classified } = emit(
      `${PT}export function f(q: Pt): number {\n` +
        `  const p: Pt = q;\n  return p.x;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toEqual({
      kind: "return",
      expr: {
        kind: "field-read",
        className: "Pt",
        field: "x",
        object: { kind: "id", name: "p" },
      },
    });
  });

  test("a method call on a class local dispatches to its class", () => {
    const { emission, classified } = emit(
      `${PT}export function f(q: Pt): number {\n` +
        `  const p: Pt = q;\n  return p.twice();\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toEqual({
      kind: "return",
      expr: {
        kind: "method-call",
        className: "Pt",
        name: "twice",
        object: { kind: "id", name: "p" },
        args: [],
      },
    });
  });

  test("a class local meets a class-typed argument slot", () => {
    const { emission, classified } = emit(
      `${PT}export function g(p: Pt): number {\n  return p.x;\n}\n` +
        `export function f(q: Pt): number {\n` +
        `  const p: Pt = q;\n  return g(p);\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[2];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toEqual({
      kind: "return",
      expr: { kind: "call", callee: "g", args: [{ kind: "id", name: "p" }] },
    });
  });

  test("a mutable class local reassigns at its class", () => {
    const { emission, classified } = emit(
      `${PT}export function f(q: Pt): number {\n` +
        `  let p: Pt = q;\n  p = new Pt(2);\n  return p.x;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn).slice(0, 2)).toEqual([
      {
        kind: "let",
        name: "p",
        init: { kind: "id", name: "q" },
        type: { class: "Pt" },
      },
      {
        kind: "assign",
        name: "p",
        expr: {
          kind: "new",
          className: "Pt",
          args: [{ kind: "num", lit: "2" }],
        },
      },
    ]);
  });

  test("a method body binds a local at its enclosing class", () => {
    const { emission, classified } = emit(
      `export class A {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new A(a).m(new A(a)) } */
  m(b: A): number {
    const other: A = b;
    return other.x;
  }
}
`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
  });

  test("an initializer that is not an instance of the class refuses at the slot", () => {
    const { classified } = emit(
      `${PT}/** @ensures{p} forall (n: int ∈ [0, 10)) { 0 <= f(n) } */\n` +
        `export function f(n: number): number {\n` +
        `  const p: Pt = n;\n  return 0;\n}\n`,
    );
    expect(classified[0]!.reason).toContain(
      "identifier 'n' is a number, not an instance of 'Pt'",
    );
  });

  test("a local at the class under construction refuses in its constructor", () => {
    const { classified } = emit(
      `export class Node {
  readonly x: number;
  constructor(x: number) {
    const me: Node = new Node(x);
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= a } */
  get v(): number {
    return this.x;
  }
}
`,
    );
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'VariableStatement' at 4:5");
  });

  test("a local at a later-declared class keeps the statement refusal", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { 0 <= f(n) } */\n` +
        `export function f(n: number): number {\n` +
        `  const p: Pt = new Pt(n);\n  return 0;\n}\n${PT}`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'VariableStatement' at 3:3",
      ],
    ]);
  });

  test("a local at a degraded class travels that class's reason", () => {
    const { classified } = emit(
      `export abstract class Bad {}\n` +
        `/** @ensures{p} forall (n: int ∈ [0, 10)) { 0 <= f(n) } */\n` +
        `export function f(n: number): number {\n` +
        `  const b: Bad = n;\n  return 0;\n}\n`,
    );
    expect(classified[0]!.reason).toMatch(/'Bad' could not be modeled/);
  });
});

describe("inferred local types (#339)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");
  const PT = `export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  twice(): number {
    return this.x * 2;
  }
}
`;

  test("an unannotated construction binds at its class", () => {
    const { emission, classified } = emit(
      `${PT}/** @ensures{p} forall (n: int ∈ [0, 10)) { 0 <= f(n) } */\n` +
        `export function f(n: number): number {\n` +
        `  const p = new Pt(n);\n  return n + p.x;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "p",
      init: { kind: "new", className: "Pt", args: [{ kind: "id", name: "n" }] },
      type: { class: "Pt" },
    });
  });

  test("an unannotated identifier binds at its parameter's class", () => {
    const { emission, classified } = emit(
      `${PT}export function f(q: Pt): number {\n` +
        `  const p = q;\n  return p.twice();\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)).toEqual([
      {
        kind: "const",
        name: "p",
        init: { kind: "id", name: "q" },
        type: { class: "Pt" },
      },
      {
        kind: "return",
        expr: {
          kind: "method-call",
          className: "Pt",
          name: "twice",
          object: { kind: "id", name: "p" },
          args: [],
        },
      },
    ]);
  });

  test("an unannotated identifier binds at an earlier local's class", () => {
    const { emission, classified } = emit(
      `${PT}export function f(n: number): number {\n` +
        `  const p = new Pt(n);\n  const r = p;\n  return r.x;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toEqual({
      kind: "const",
      name: "r",
      init: { kind: "id", name: "p" },
      type: { class: "Pt" },
    });
  });

  test("an unannotated class-typed field read binds at the field's class", () => {
    const { emission, classified } = emit(
      `${PT}export class Box {
  readonly p: Pt;
  constructor(p: Pt) {
    this.p = p;
  }
}
export function f(b: Box): number {
  const q = b.p;
  return q.x;
}
`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[2];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "q",
      init: {
        kind: "field-read",
        className: "Box",
        field: "p",
        object: { kind: "id", name: "b" },
      },
      type: { class: "Pt" },
    });
  });

  test("an unannotated identifier binds at its parameter's union", () => {
    const { emission, classified } = emit(
      `export function f(v: number | string): number {\n` +
        `  const w = v;\n  return typeof w === "number" ? w : 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "w",
      init: { kind: "id", name: "v" },
      type: ["number", "string"],
    });
  });

  test("a number-valued initializer still binds at number", () => {
    const { emission, classified } = emit(
      `${PT}export function f(q: Pt): number {\n` +
        `  const m = q.x + 1;\n  const t = q.twice();\n  return m + t;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).not.toHaveProperty("type");
    expect(fnBody(fn)[1]).not.toHaveProperty("type");
  });

  test("an explicit annotation stays authoritative over the initializer", () => {
    const { classified } = emit(
      `${PT}/** @ensures{p} forall (q: Pt) { 0 <= f(q) } */\n` +
        `export function f(q: Pt): number {\n` +
        `  const m: number = q;\n  return 0;\n}\n`,
    );
    expect(classified[0]!.reason).toContain(
      "identifier 'q' is an instance of 'Pt', not a number",
    );
  });

  test("an unannotated mutable local reassigns at its inferred class", () => {
    const { emission, classified } = emit(
      `${PT}export function f(n: number): number {\n` +
        `  let p = new Pt(n);\n  p = new Pt(p.x + 1);\n  return p.x;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toMatchObject({
      kind: "let",
      name: "p",
      type: { class: "Pt" },
    });
    expect(fnBody(fn)[1]).toMatchObject({ kind: "assign", name: "p" });
  });

  test("an arm's inferred local reads as a place inside the arm", () => {
    const { emission, classified } = emit(
      `${PT}export function f(n: number): number {\n` +
        `  if (n > 0) {\n    const p = new Pt(n);\n    return p.x;\n  }\n` +
        `  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
  });

  test("a construction at a later-declared class refuses the statement", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { 0 <= f(n) } */\n` +
        `export function f(n: number): number {\n` +
        `  const p = new Pt(n);\n  return p.x;\n}\n${PT}`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'VariableStatement' at 3:3",
      ],
    ]);
  });

  test("a construction at a degraded class travels that class's reason", () => {
    const { classified } = emit(
      `export abstract class Bad {}\n` +
        `/** @ensures{p} forall (n: int ∈ [0, 10)) { 0 <= f(n) } */\n` +
        `export function f(n: number): number {\n` +
        `  const b = new Bad();\n  return 0;\n}\n`,
    );
    expect(classified[0]!.reason).toMatch(/'Bad' could not be modeled/);
  });

  test("a construction of the class under construction refuses in its constructor", () => {
    const { classified } = emit(
      `export class Node {
  readonly x: number;
  constructor(x: number) {
    const me = new Node(x);
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= a } */
  get v(): number {
    return this.x;
  }
}
`,
    );
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'VariableStatement' at 4:5");
  });

  test("a local bound to this refuses at the initializer", () => {
    const src = `export class A {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { 0 <= new A(a).m() } */
  m(): number {
    const me = this;
    return me.x;
  }
}
`;
    expect(residualConstructs(src)).toEqual([
      "unmapped TypeScript construct 'ThisKeyword' at 8:16",
      // The local is bound to the site, so its read is a site of its own.
      "unmapped TypeScript construct 'PropertyAccessExpression' at 9:12",
    ]);
  });
});

describe("optional parameters", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  /** A module's first declaration's parameters, narrowed. */
  const paramsOf = (src: string) => {
    const fn = emit(src).emission.declarations[0];
    assert(fn !== undefined && fn.kind === "function");
    return fn.params;
  };

  test("an optional parameter unions undefined into its declared type", () => {
    expect(
      paramsOf(
        `export function f(a: number, b?: number, c?: string, d?: number | string): number {\n  return a;\n}\n`,
      ),
    ).toEqual([
      { name: "a", type: "number" },
      { name: "b", type: ["number", "undefined"] },
      { name: "c", type: ["string", "undefined"] },
      { name: "d", type: ["number", "string", "undefined"] },
    ]);
  });

  test("an optional carries the wire shape of the equivalent explicit union", () => {
    expect(
      paramsOf(`export function f(b?: number): number {\n  return 0;\n}\n`),
    ).toEqual(
      paramsOf(
        `export function f(b: number | undefined): number {\n  return 0;\n}\n`,
      ),
    );
  });

  test("an optional whose type joins no keyword union keeps its refusal", () => {
    const { classified } = emit(
      `export class C {\n  v: number;\n  constructor(v: number) {\n    this.v = v;\n  }\n}\n` +
        `/** @ensures{p} forall (x: number) { Object.is(f(x), x) } */\n` +
        `export function f(c?: C): number {\n  return 0;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'Parameter' at 8:19",
      ],
    ]);
  });

  test("an optional whose widened union is still one tag refuses at the type", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), x) } */\n` +
        `export function f(v?: undefined): number {\n  return 0;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'UndefinedKeyword' at 2:23",
      ],
    ]);
  });

  test("a required parameter following an optional one refuses at that parameter", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), x) } */\n` +
        `export function f(a?: number, b: number): number {\n  return 0;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'Parameter' at 2:31",
      ],
    ]);
  });

  test("a call omitting a trailing optional injects undefined", () => {
    const { emission } = emit(
      `export function pick(y?: number): number {\n  if (y === undefined) {\n    return 0;\n  }\n  return y;\n}\n` +
        `export function call(): number {\n  return pick();\n}\n`,
    );
    expect(fnBody(emission.declarations[1]!)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "call",
        callee: "pick",
        args: [{ kind: "inject", tag: "undefined" }],
      },
    });
  });

  test("a call supplying the optional injects at the argument's own tag", () => {
    const { emission } = emit(
      `export function pick(y?: number): number {\n  return 0;\n}\n` +
        `export function call(x: number): number {\n  return pick(x);\n}\n`,
    );
    expect(fnBody(emission.declarations[1]!)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "call",
        callee: "pick",
        args: [
          { kind: "inject", tag: "number", expr: { kind: "id", name: "x" } },
        ],
      },
    });
  });

  test("under-arity against a required parameter and over-arity stay the engine's error", () => {
    const call = (args: string) =>
      emit(
        `/** @ensures{p} forall (x: number) { Object.is(call(x), x) } */\n` +
          `export function f(a: number, b?: number): number {\n  return a;\n}\n` +
          `export function call(x: number): number {\n  return f(${args});\n}\n`,
      ).classified;

    expect(call("").map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "property elaboration failed: 'call' has no model: " +
          "'f' expects 1 to 2 argument(s), got 0",
      ],
    ]);
    expect(call("x, 1, 2").map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "property elaboration failed: 'call' has no model: " +
          "'f' expects 1 to 2 argument(s), got 3",
      ],
    ]);
  });

  test("a function with no optionals keeps the unchanged arity message", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(call(x), x) } */\n` +
        `export function f(a: number): number {\n  return a;\n}\n` +
        `export function call(x: number): number {\n  return f(x, 1);\n}\n`,
    );
    expect(classified[0]?.reason).toContain("'f' expects 1 argument(s), got 2");
  });

  test("a constructor keeps the optional ban", () => {
    const src =
      `export class C {\n  v: number;\n  constructor(v: number, w?: number) {\n    this.v = v;\n  }\n}\n` +
      `/** @ensures{p} forall (x: number) { Object.is(get(x), x) } */\n` +
      `export function get(x: number): number {\n  return new C(x, 1).v;\n}\n`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'Parameter' at 3:26",
      ),
    ]);
  });

  test("a method admits an optional, and its call may omit it", () => {
    const { emission } = emit(
      `export class C {\n  v: number;\n  constructor(v: number) {\n    this.v = v;\n  }\n` +
        `  m(k?: number): number {\n    return this.v;\n  }\n}\n` +
        `export function call(x: number): number {\n  return new C(x).m();\n}\n`,
    );
    const cls = emission.declarations[0];
    assert(cls !== undefined && cls.kind === "class");
    expect(cls.methods[0]?.params).toEqual([
      { name: "k", type: ["number", "undefined"] },
    ]);
    expect(fnBody(emission.declarations[1]!)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "method-call",
        className: "C",
        name: "m",
        object: {
          kind: "new",
          className: "C",
          args: [{ kind: "id", name: "x" }],
        },
        args: [{ kind: "inject", tag: "undefined" }],
      },
    });
  });

  test("a method's under-arity against a required parameter stays an error", () => {
    const { classified } = emit(
      `export class C {\n  v: number;\n  constructor(v: number) {\n    this.v = v;\n  }\n` +
        `  m(j: number, k?: number): number {\n    return this.v;\n  }\n}\n` +
        `/** @ensures{p} forall (x: number) { Object.is(call(x), x) } */\n` +
        `export function call(x: number): number {\n  return new C(x).m();\n}\n`,
    );
    expect(classified[0]?.szs).toBe("Error");
    expect(classified[0]?.reason).toContain(
      "'C#m' expects 1 to 2 argument(s), got 0",
    );
  });
});

describe("refused annotations", () => {
  const src =
    "/** @ensures{a} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
    "/** @ensures{b} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
    "export function f(x: number): number { return x; }\n";

  test("a refused annotation is neither emitted nor classified, and its sibling still is", () => {
    const refused = new Set([
      annotationKey("t.ts", { functionName: "f", propertyName: "a" }),
    ]);
    const { emission, annotations, classified } = emitModule(
      src,
      "t.ts",
      undefined,
      refused,
    );
    expect(annotations.map((a) => a.propertyName)).toEqual(["b"]);
    expect(classified).toEqual([]);
    expect(emission.obligations.map((o) => o.property)).toEqual(["b"]);
  });
});

describe("fields beyond number", () => {
  const INNER = `export class Inner {
  readonly v: number;
  constructor(v: number) {
    this.v = v;
  }
}
`;
  /** A class over a union field and a number field; the annotation reads
   * only the number field, so the union field is stored and never read. */
  function withField(field: string, set: string): string {
    return `${INNER}export class C {
  readonly x: ${field};
  readonly n: number;
  constructor(n: number, i: Inner) {
    this.x = ${set};
    this.n = n;
  }
  /** @ensures{p} forall (a: number) { Object.is(new C(a, new Inner(a)).v, a) } */
  get v(): number {
    return this.n;
  }
}
`;
  }
  function classC(src: string): EmitClass {
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    return emission.declarations[1] as EmitClass;
  }
  function setOf(cls: EmitClass): Extract<EmitStmt, { kind: "field-set" }> {
    const s = cls.ctor.body[0]!;
    assert(s.kind === "field-set");
    return s;
  }

  test("a number | undefined field models, its write injecting the number", () => {
    const cls = classC(withField("number | undefined", "n"));
    expect(cls.fields).toEqual([
      { name: "x", type: ["number", "undefined"] },
      { name: "n" },
    ]);
    expect(setOf(cls)).toEqual({
      kind: "field-set",
      field: "x",
      expr: { kind: "inject", tag: "number", expr: { kind: "id", name: "n" } },
    });
  });

  test("the undefined and null atoms inject at their tags", () => {
    expect(
      setOf(classC(withField("number | undefined", "undefined"))).expr,
    ).toEqual({ kind: "inject", tag: "undefined" });
    expect(setOf(classC(withField("number | null", "null"))).expr).toEqual({
      kind: "inject",
      tag: "null",
    });
  });

  test("a union spelling normalizes as a parameter's does, one member collapsing", () => {
    expect(
      classC(withField("undefined | number | number", "n")).fields[0],
    ).toEqual({
      name: "x",
      type: ["number", "undefined"],
    });
    expect(classC(withField("number | number", "n")).fields[0]).toEqual({
      name: "x",
    });
  });

  test("a union local in the constructor flows to a field of the same spelling", () => {
    const src = `export class C {
  readonly x: number | undefined;
  constructor(n: number) {
    const w: number | undefined = n;
    this.x = w;
  }
  /** @ensures{p} forall (a: number) { Object.is(new C(a).v, a) } */
  get v(): number {
    return 0 * 1 + 0;
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.ctor.body[1]).toEqual({
      kind: "field-set",
      field: "x",
      expr: { kind: "id", name: "w" },
    });
  });

  test("a class-typed field at an earlier class models, its write an instance", () => {
    const cls = classC(withField("Inner", "i"));
    expect(cls.fields[0]).toEqual({ name: "x", type: { class: "Inner" } });
    expect(setOf(cls).expr).toEqual({ kind: "id", name: "i" });
    expect(setOf(classC(withField("Inner", "new Inner(n)"))).expr).toEqual({
      kind: "new",
      className: "Inner",
      args: [{ kind: "id", name: "n" }],
    });
    expect(
      setOf(classC(withField("Inner", "n < 0 ? i : new Inner(n)"))).expr.kind,
    ).toBe("cond");
  });

  test.each([
    [
      "a self-typed field",
      "C",
      "i",
      "unmapped TypeScript construct 'TypeReference'",
    ],
    [
      "a field at a later class",
      "Later",
      "i",
      "unmapped TypeScript construct 'TypeReference'",
    ],
    [
      "a literal member",
      "number | 'a'",
      "n",
      "unmapped TypeScript construct 'LiteralType'",
    ],
    [
      "a lone string",
      "string",
      "n",
      "unmapped TypeScript construct 'StringKeyword'",
    ],
  ])("%s refuses the class", (_what, field, set, reason) => {
    const src =
      withField(field, set) + "export class Later {\n  constructor() {}\n}\n";
    const { classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(reason);
  });

  test("a field at a degraded class travels that class's reason", () => {
    const src = `export class Bad {
  constructor(...xs: number[]) {}
}
export class C {
  readonly b: Bad;
  constructor(b: Bad) {
    this.b = b;
  }
  /** @ensures{p} forall (a: number) { Object.is(new C(new Bad()).v, a) } */
  get v(): number {
    return 0;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toContain(
      "'Bad' could not be modeled: unmapped TypeScript construct 'DotDotDotToken'",
    );
  });

  test("a write typed at the field refuses a mismatch", () => {
    const { classified } = emitModule(withField("Inner", "n"), "t.ts");
    expect(classified[0]!.reason).toContain(
      "identifier 'n' is a number, not an instance of 'Inner'",
    );
  });

  test("a read of a non-number field refuses until it is a place", () => {
    const src = `${INNER}export class C {
  readonly inner: Inner;
  constructor(i: Inner) {
    this.inner = i;
  }
  /** @ensures{p} forall (a: number) { Object.is(new C(new Inner(a)).v, a) } */
  get v(): number {
    return this.inner;
  }
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toContain(
      "field 'inner' is an instance of 'Inner', not a number",
    );
  });

  /** A class over a `number | undefined` field, with a method body `m`
   * and a free function `f` over the class, both annotated. */
  function unionField(method: string, fn = "return 0;"): string {
    return `export class R {
  readonly x: number | undefined;
  constructor(n: number) {
    this.x = n;
  }
  /** @ensures{m} forall (a: number) { Object.is(new R(a).m(), new R(a).m()) } */
  m(): number {
    ${method}
  }
}
/** @ensures{f} forall (a: number) { Object.is(f(new R(a)), f(new R(a))) } */
export function f(r: R): number {
  ${fn}
}
`;
  }
  function bodyOf(src: string, which: "m" | "f"): EmitStmt[] {
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    return which === "m"
      ? (emission.declarations[0] as EmitClass).methods[0]!.body
      : fnBody(emission.declarations[1]!);
  }
  const SELF_X: EmitExpr = {
    kind: "field-read",
    className: "R",
    field: "x",
    object: { kind: "self" },
  };

  test("a union field at a number position is the throwing projection", () => {
    expect(bodyOf(unionField("return this.x;"), "m")[0]).toEqual({
      kind: "return",
      expr: { kind: "project", tag: "number", expr: SELF_X },
    });
    expect(bodyOf(unionField("return 0;", "return r.x;"), "f")[0]).toEqual({
      kind: "return",
      expr: {
        kind: "project",
        tag: "number",
        expr: {
          kind: "field-read",
          className: "R",
          field: "x",
          object: { kind: "id", name: "r" },
        },
      },
    });
  });

  test("typeof narrows a union field read", () => {
    const body = bodyOf(
      unionField(
        'if (typeof this.x === "number") {\n      return this.x;\n    }\n    return 0;',
      ),
      "m",
    );
    expect(body[0]).toMatchObject({
      kind: "if",
      cond: { kind: "typeof-test", expr: SELF_X, result: "number" },
    });
  });

  test("strict equality and Object.is on a union field read lower over JsVal", () => {
    expect(
      bodyOf(unionField("return this.x === undefined ? 0 : this.x;"), "m")[0],
    ).toEqual({
      kind: "return",
      expr: {
        kind: "cond",
        cond: {
          kind: "jsval-eq",
          semantics: "strict",
          left: SELF_X,
          right: { kind: "inject", tag: "undefined" },
        },
        then: { kind: "num", lit: "0" },
        else: { kind: "project", tag: "number", expr: SELF_X },
      },
    });
    expect(
      bodyOf(
        unionField("return Object.is(this.x, undefined) ? 1 : 0;"),
        "m",
      )[0],
    ).toMatchObject({
      expr: {
        cond: { kind: "jsval-eq", semantics: "same-value", left: SELF_X },
      },
    });
  });

  test("Object.is over a field read in a formula atom", () => {
    const src = `export class R {
  readonly x: number | undefined;
  constructor(n: number) {
    this.x = n;
  }
}
/** @ensures{p} forall (a: number) { Object.is(new R(a).x, undefined) } */
export function f(a: number): number {
  return a;
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(JSON.stringify(emission.obligations[0])).toContain(
      '"semantics":"same-value"',
    );
  });

  test("a union field read flows to a union local and a union parameter of the same spelling", () => {
    // `take` is declared first: a method body resolves free functions
    // from the registry the walk fills in source order.
    const src = `export function take(v: number | undefined): number {
  return 0;
}
export class R {
  readonly x: number | undefined;
  constructor(n: number) {
    this.x = n;
  }
  /** @ensures{m} forall (a: number) { Object.is(new R(a).m(), new R(a).m()) } */
  m(): number {
    const w: number | undefined = this.x;
    return take(w) + take(this.x);
  }
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    const body = (emission.declarations[1] as EmitClass).methods[0]!.body;
    expect(body[0]).toMatchObject({ kind: "const", name: "w", init: SELF_X });
    expect(body[1]).toMatchObject({
      expr: { right: { kind: "call", callee: "take", args: [SELF_X] } },
    });
  });

  /** A class over a `boolean | undefined` field, with a method body `m`
   * and a free function `f` over the class, both annotated. */
  function boolUnionField(method: string, fn = "return 0;"): string {
    return `export class B {
  readonly on: boolean | undefined;
  constructor(n: number) {
    this.on = n > 0;
  }
  /** @ensures{m} forall (a: number) { Object.is(new B(a).m(), new B(a).m()) } */
  m(): number {
    ${method}
  }
}
/** @ensures{f} forall (a: number) { Object.is(f(new B(a)), f(new B(a))) } */
export function f(b: B): number {
  ${fn}
}
`;
  }
  function boolBodyOf(src: string, which: "m" | "f"): EmitStmt[] {
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    return which === "m"
      ? (emission.declarations[0] as EmitClass).methods[0]!.body
      : fnBody(emission.declarations[1]!);
  }
  const SELF_ON: EmitExpr = {
    kind: "field-read",
    className: "B",
    field: "on",
    object: { kind: "self" },
  };

  test("a boolean-carrying union place projects under a logical operator", () => {
    expect(
      boolBodyOf(
        boolUnionField(
          'if (typeof this.on === "boolean" && this.on) {\n      return 1;\n    }\n    return 0;',
        ),
        "m",
      )[0],
    ).toMatchObject({
      kind: "if",
      cond: {
        kind: "binop",
        op: "&&",
        right: { kind: "project", tag: "boolean", expr: SELF_ON },
      },
    });
  });

  test("a boolean-carrying union place projects as a bare condition", () => {
    expect(
      boolBodyOf(
        boolUnionField("if (this.on) {\n      return 1;\n    }\n    return 0;"),
        "m",
      )[0],
    ).toMatchObject({
      kind: "if",
      cond: { kind: "project", tag: "boolean", expr: SELF_ON },
    });
  });

  test("a boolean-carrying union place on a parameter receiver projects", () => {
    expect(
      boolBodyOf(boolUnionField("return 0;", "return b.on ? 1 : 0;"), "f")[0],
    ).toMatchObject({
      kind: "return",
      expr: {
        kind: "cond",
        cond: {
          kind: "project",
          tag: "boolean",
          expr: {
            kind: "field-read",
            className: "B",
            field: "on",
            object: { kind: "id", name: "b" },
          },
        },
      },
    });
  });

  test("a boolean-carrying union local projects at a boolean position", () => {
    expect(
      boolBodyOf(
        boolUnionField(
          "const w: boolean | undefined = this.on;\n    if (w) {\n      return 1;\n    }\n    return 0;",
        ),
        "m",
      )[1],
    ).toMatchObject({
      kind: "if",
      cond: {
        kind: "project",
        tag: "boolean",
        expr: { kind: "id", name: "w" },
      },
    });
  });

  test("a union carrying no boolean records its site at a boolean position", () => {
    // Truthiness has no model for a union that cannot hold a boolean, so
    // the condition becomes a site naming the read it could not map.
    const src = unionField(
      "if (this.x) {\n      return 1;\n    }\n    return 0;",
    );
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("PropertyAccessExpression"),
    ]);
  });

  test("a local inferred from a boolean-carrying union place keeps the union", () => {
    const { classified } = emitModule(
      boolUnionField(
        "const w = this.on;\n    const v: boolean | undefined = w;\n    return 0;",
      ),
      "t.ts",
    );
    expect(classified).toEqual([]);
  });

  test("a union field read at a wider union spelling refuses", () => {
    const src = unionField(
      "const w: number | string | undefined = this.x;\n    return 0;",
    );
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("unions flow only between identical spellings"),
    ]);
  });

  test("typeof on a number field is still outside the model", () => {
    const src = `export class R {
  readonly n: number;
  constructor(n: number) {
    this.n = n;
  }
  /** @ensures{m} forall (a: number) { Object.is(new R(a).m(), 0) } */
  m(): number {
    if (typeof this.n === "number") {
      return 0;
    }
    return 1;
  }
}
`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'TypeOfExpression'",
      ),
    ]);
  });

  const NESTED = `export class Inner {
  readonly v: number;
  readonly u: number | undefined;
  constructor(v: number) {
    this.v = v;
    this.u = v;
  }
  get twice(): number {
    return this.v * 2;
  }
  double(): number {
    return this.v * 2;
  }
}
export function takeInner(i: Inner): number {
  return i.v;
}
export class Outer {
  readonly inner: Inner;
  constructor(i: Inner) {
    this.inner = i;
  }
  /** @ensures{m} forall (a: number) { Object.is(new Outer(new Inner(a)).m(), new Outer(new Inner(a)).m()) } */
  m(): number {
    BODY
  }
}
/** @ensures{f} forall (a: number) { Object.is(f(new Outer(new Inner(a))), f(new Outer(new Inner(a)))) } */
export function f(o: Outer): number {
  return o.inner.v;
}
`;
  const SELF_INNER: EmitExpr = {
    kind: "field-read",
    className: "Outer",
    field: "inner",
    object: { kind: "self" },
  };
  function nestedBody(body: string): EmitStmt[] {
    const src = NESTED.replace("BODY", body);
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    return (emission.declarations[2] as EmitClass).methods[0]!.body;
  }

  test("a field read on an instance field is a nested field read", () => {
    expect(nestedBody("return this.inner.v;")[0]).toEqual({
      kind: "return",
      expr: {
        kind: "field-read",
        className: "Inner",
        field: "v",
        object: SELF_INNER,
      },
    });
  });

  test("a getter and a method dispatch on an instance field", () => {
    expect(nestedBody("return this.inner.twice;")[0]).toEqual({
      kind: "return",
      expr: {
        kind: "getter-read",
        className: "Inner",
        name: "twice",
        object: SELF_INNER,
      },
    });
    expect(nestedBody("return this.inner.double();")[0]).toEqual({
      kind: "return",
      expr: {
        kind: "method-call",
        className: "Inner",
        name: "double",
        object: SELF_INNER,
        args: [],
      },
    });
  });

  test("a union field two levels down projects and narrows", () => {
    expect(nestedBody("return this.inner.u;")[0]).toEqual({
      kind: "return",
      expr: {
        kind: "project",
        tag: "number",
        expr: {
          kind: "field-read",
          className: "Inner",
          field: "u",
          object: SELF_INNER,
        },
      },
    });
  });

  test("an instance field flows to a class-typed parameter", () => {
    expect(nestedBody("return takeInner(this.inner);")[0]).toEqual({
      kind: "return",
      expr: { kind: "call", callee: "takeInner", args: [SELF_INNER] },
    });
  });

  test("a class-typed parameter's instance field is a receiver, and a fresh instance's too", () => {
    const src = NESTED.replace("BODY", "return 0;");
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(fnBody(emission.declarations[3]!)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "field-read",
        className: "Inner",
        field: "v",
        object: {
          kind: "field-read",
          className: "Outer",
          field: "inner",
          object: { kind: "id", name: "o" },
        },
      },
    });
    const atom = `export class Inner {
  readonly v: number;
  constructor(v: number) {
    this.v = v;
  }
}
export class Outer {
  readonly inner: Inner;
  constructor(i: Inner) {
    this.inner = i;
  }
}
/** @ensures{p} forall (a: number) { Object.is(new Outer(new Inner(a)).inner.v, a) } */
export function g(a: number): number {
  return a;
}
`;
    const r = emitModule(atom, "t.ts");
    expect(r.classified).toEqual([]);
    expect(JSON.stringify(r.emission.obligations[0])).toContain(
      '"field":"inner"',
    );
  });

  test.each([
    [
      "an instance field at a number position",
      "return this.inner;",
      "field 'inner' is an instance of 'Inner', not a number",
    ],
    [
      "a member the model lacks",
      "return this.inner.nope;",
      "'Inner' has no member 'nope' in the model",
    ],
    [
      "a method the model lacks",
      "return this.inner.nope();",
      "'Inner' has no method 'nope' in the model",
    ],
    [
      "a member on this the model lacks",
      "return this.nope;",
      "'this.nope' does not name a field or a modeled getter of 'Outer'",
    ],
  ])("%s refuses", (_what, body, reason) => {
    const src = NESTED.replace("BODY", body).replace(
      "  /** @ensures{m}",
      "  get twice(): number {\n    return 1;\n  }\n  /** @ensures{m}",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified.map((c) => c.reason).join("\n")).toContain(reason);
  });

  test("the scan reports a construct inside a nested receiver's arguments", () => {
    const src = NESTED.replace("BODY", "return new Inner(this.inner.v!).v;");
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'NonNullExpression'",
      ),
    ]);
  });

  test("an unmodelable member reached through a field owns its site", () => {
    const src = `export class Inner {
  readonly v: number;
  constructor(v: number) {
    this.v = v;
  }
  broken(): number {
    return this.v ** 2;
  }
}
export class Outer {
  readonly inner: Inner;
  constructor(i: Inner) {
    this.inner = i;
  }
  /** @ensures{m} forall (a: number) { Object.is(new Outer(new Inner(a)).m(), 0) } */
  m(): number {
    return this.inner.broken();
  }
}
`;
    expect(residualConstructs(src)).toEqual(["'**' is not supported"]);
    expect(residualOwners(src)).toEqual(["Inner#broken"]);
  });

  test.each([
    [
      "a call as a receiver",
      "return takeInner(this.inner).nope;",
      "unmapped TypeScript construct 'PropertyAccessExpression'",
    ],
    [
      "a chain through a member the class lacks",
      "return this.nope.v;",
      "unmapped TypeScript construct 'PropertyAccessExpression'",
    ],
  ])("%s is outside the model", (_what, body, reason) => {
    expect(residualConstructs(NESTED.replace("BODY", body))).toEqual([
      expect.stringContaining(reason),
    ]);
  });

  test("the scan reaches a construct in a nested call's argument", () => {
    const src = NESTED.replace(
      "BODY",
      "return this.inner.double() + new Inner(await h()).v;",
    );
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'AwaitExpression'",
      ),
    ]);
  });

  test("a builtin member call is still numeric-shaped beside the place rule", () => {
    const src = `/** @ensures{p} forall (a: number) { Object.is(Math.abs(a), g(a)) } */
export function g(a: number): number {
  return Math.abs(a);
}
`;
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(JSON.stringify(emission.obligations[0])).toContain(
      '"kind":"builtin","object":"Math","member":"abs"',
    );
  });

  test("an unsupported operator inside a plain call's argument still names it", () => {
    const src = `export function h(a: number): number {
  return a;
}
/** @ensures{p} forall (a: number) { Object.is(h(a ** 2), a) } */
export function g(a: number): number {
  return a;
}
`;
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toContain("'**' is not supported");
  });

  test("the scan reports a construct inside a builtin call's argument", () => {
    const src = `/** @ensures{p} forall (a: number) { Object.is(g(a), a) } */
export function g(a: number): number {
  return Math.abs(a!);
}
`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining(
        "unmapped TypeScript construct 'NonNullExpression'",
      ),
    ]);
  });

  test("a degraded declaration inside a builtin call's argument travels", () => {
    const src = `export class Bad {
  constructor(...xs: number[]) {}
}
/** @ensures{p} forall (a: number) { Object.is(g(a), a) } */
export function g(a: number): number {
  return Math.abs(new Bad(a).v);
}
`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("'Bad' could not be modeled"),
    ]);
  });
});

describe("boolean locals (#117)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("an annotated boolean local with a literal initializer binds at boolean", () => {
    const { emission, classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */\n` +
        `export function f(n: number): number {\n` +
        `  const ok: boolean = true;\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "ok",
      init: { kind: "bool", value: true },
      type: "boolean",
    });
  });

  test("an annotated boolean local takes a comparison", () => {
    const { emission, classified } = emit(
      `export function f(n: number): number {\n` +
        `  const small: boolean = n < 5;\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "small",
      init: {
        kind: "binop",
        op: "<",
        left: { kind: "id", name: "n" },
        right: { kind: "num", lit: "5" },
      },
      type: "boolean",
    });
  });

  test("a numeric initializer cannot bind a boolean local", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */\n` +
        `export function f(n: number): number {\n` +
        `  const ok: boolean = 5;\n  return n;\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "a numeric literal cannot be a boolean",
    );
  });

  test("a boolean literal cannot stand where a number is expected", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */\n` +
        `export function f(n: number): number {\n  return true;\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "a boolean literal cannot be a number",
    );
  });
});

describe("inferred boolean locals and bound boolean names (#117)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("an unannotated comparison binds at boolean and names a condition", () => {
    const { emission, classified } = emit(
      `/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { clip(n) >= 0 } */\n` +
        `export function clip(n: number): number {\n` +
        `  const isSmall = n < 5;\n  if (isSmall) {\n    return 0;\n  }\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)).toEqual([
      {
        kind: "const",
        name: "isSmall",
        init: {
          kind: "binop",
          op: "<",
          left: { kind: "id", name: "n" },
          right: { kind: "num", lit: "5" },
        },
        type: "boolean",
      },
      {
        kind: "if",
        cond: { kind: "id", name: "isSmall" },
        then: [{ kind: "return", expr: { kind: "num", lit: "0" } }],
      },
      { kind: "return", expr: { kind: "id", name: "n" } },
    ]);
  });

  test("the flag idiom: a mutable boolean set in an arm and read after", () => {
    const { emission, classified } = emit(
      `export function flag(n: number): number {\n` +
        `  let found = false;\n  if (n < 5) {\n    found = true;\n  }\n` +
        `  if (found) {\n    return 0;\n  }\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "let",
      name: "found",
      init: { kind: "bool", value: false },
      type: "boolean",
    });
    expect(fnBody(fn)[1]).toMatchObject({
      kind: "if",
      then: [
        { kind: "assign", name: "found", expr: { kind: "bool", value: true } },
      ],
    });
    expect(fnBody(fn)[2]).toMatchObject({
      kind: "if",
      cond: { kind: "id", name: "found" },
    });
  });

  test("a bound boolean is a logical operand and a negation operand", () => {
    const { emission, classified } = emit(
      `export function f(n: number): number {\n` +
        `  const a = n < 5;\n  const b = !a;\n` +
        `  if (a && n > 1) {\n    return 1;\n  }\n  if (b) {\n    return 2;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toEqual({
      kind: "const",
      name: "b",
      init: { kind: "unop", op: "!", operand: { kind: "id", name: "a" } },
      type: "boolean",
    });
    expect(fnBody(fn)[2]).toMatchObject({
      kind: "if",
      cond: { kind: "binop", op: "&&", left: { kind: "id", name: "a" } },
    });
  });

  test("a boolean local is not a number", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */\n` +
        `export function f(n: number): number {\n` +
        `  const isSmall = n < 5;\n  return isSmall;\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "identifier 'isSmall' is a boolean, not a number",
    );
  });

  test("truthiness of a number local records its construct at the site", () => {
    const src =
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */\n` +
      `export function f(n: number): number {\n` +
      `  const x = n + 1;\n  if (x) {\n    return 0;\n  }\n  return n;\n}\n`;
    expect(residualConstructs(src)).toEqual([
      expect.stringContaining("unmapped TypeScript construct 'Identifier'"),
    ]);
  });
});

describe("boolean equality and union slots (#117)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("strict equality on booleans lowers over the tagged domain", () => {
    const { emission, classified } = emit(
      `export function f(n: number): number {\n` +
        `  const a = n < 5;\n  if (a === true) {\n    return 0;\n  }\n` +
        `  if (a !== (n > 7)) {\n    return 1;\n  }\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toMatchObject({
      kind: "if",
      cond: {
        kind: "jsval-eq",
        semantics: "strict",
        left: {
          kind: "inject",
          tag: "boolean",
          expr: { kind: "id", name: "a" },
        },
        right: {
          kind: "inject",
          tag: "boolean",
          expr: { kind: "bool", value: true },
        },
      },
    });
    expect(fnBody(fn)[2]).toMatchObject({
      kind: "if",
      cond: {
        kind: "unop",
        op: "!",
        operand: { kind: "jsval-eq", semantics: "strict" },
      },
    });
  });

  test("Object.is on a bound boolean and a literal", () => {
    const { emission, classified } = emit(
      `export function f(n: number): number {\n` +
        `  const a = n < 5;\n  if (Object.is(a, false)) {\n    return 0;\n  }\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toMatchObject({
      kind: "if",
      cond: {
        kind: "jsval-eq",
        semantics: "same-value",
        left: {
          kind: "inject",
          tag: "boolean",
          expr: { kind: "id", name: "a" },
        },
        right: {
          kind: "inject",
          tag: "boolean",
          expr: { kind: "bool", value: false },
        },
      },
    });
  });

  test("a boolean-shaped expression meets a union slot carrying boolean", () => {
    const { emission, classified } = emit(
      `export function f(n: number): number {\n` +
        `  const w: boolean | undefined = n < 5;\n` +
        `  if (typeof w === "boolean") {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toEqual({
      kind: "const",
      name: "w",
      init: {
        kind: "inject",
        tag: "boolean",
        expr: {
          kind: "binop",
          op: "<",
          left: { kind: "id", name: "n" },
          right: { kind: "num", lit: "5" },
        },
      },
      type: ["boolean", "undefined"],
    });
  });

  test("a boolean cannot flow to a union slot without a boolean member", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */\n` +
        `export function f(n: number): number {\n` +
        `  const w: number | undefined = n < 5;\n  return 0;\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "slot has no 'boolean' member, so a boolean-valued expression cannot flow to it",
    );
  });
});

describe("boolean parameters (#354)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("a boolean parameter binds at boolean and rides the wire as its keyword", () => {
    const { emission, classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 10)) (b: boolean) { pick(n, b) >= 0 } */\n` +
        `export function pick(n: number, b: boolean): number {\n` +
        `  if (b) {\n    return n;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.params).toEqual([
      { name: "n", type: "number" },
      { name: "b", type: "boolean" },
    ]);
    expect(fnBody(fn)[0]).toMatchObject({
      kind: "if",
      cond: { kind: "id", name: "b" },
    });
  });

  test("a boolean parameter is a logical operand and an equality side", () => {
    const { classified, emission } = emit(
      `export function f(n: number, b: boolean): number {\n` +
        `  if (!b && n > 1) {\n    return 1;\n  }\n` +
        `  if (b === (n < 3)) {\n    return 2;\n  }\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[1]).toMatchObject({
      kind: "if",
      cond: { kind: "jsval-eq", semantics: "strict" },
    });
  });

  test("a boolean parameter is not a number", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (b: boolean) { f(b) >= 0 } */\n` +
        `export function f(b: boolean): number {\n  return b;\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "identifier 'b' is a boolean, not a number",
    );
  });

  test("an argument meeting a boolean slot walks at boolean", () => {
    const { classified, emission } = emit(
      `export function pick(n: number, b: boolean): number {\n` +
        `  if (b) {\n    return n;\n  }\n  return 0;\n}\n` +
        `export function g(n: number): number {\n  return pick(n, n < 5);\n}\n`,
    );
    expect(classified).toEqual([]);
    const g = emission.declarations[1];
    assert(g?.kind === "function");
    expect(fnBody(g)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "call",
        callee: "pick",
        args: [
          { kind: "id", name: "n" },
          {
            kind: "binop",
            op: "<",
            left: { kind: "id", name: "n" },
            right: { kind: "num", lit: "5" },
          },
        ],
      },
    });
  });

  test("a number meeting a boolean slot is the engine's type error", () => {
    const { classified } = emit(
      `export function pick(n: number, b: boolean): number {\n` +
        `  if (b) {\n    return n;\n  }\n  return 0;\n}\n` +
        `/** @ensures{p} forall (n: int ∈ [0, 3)) { g(n) >= 0 } */\n` +
        `export function g(n: number): number {\n  return pick(n, n);\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "identifier 'n' is a number, not a boolean",
    );
  });

  test("a method takes a boolean parameter", () => {
    const { classified, emission } = emit(
      `export class Gate {\n  readonly level: number;\n` +
        `  constructor(level: number) {\n    this.level = level;\n  }\n` +
        `  pass(n: number, force: boolean): number {\n` +
        `    if (force) {\n      return n;\n    }\n    return this.level;\n  }\n}\n`,
    );
    expect(classified).toEqual([]);
    const cls = emission.declarations[0];
    assert(cls?.kind === "class");
    expect(cls.methods[0]!.params).toEqual([
      { name: "n", type: "number" },
      { name: "force", type: "boolean" },
    ]);
  });
});

describe("booleans in classes (#355)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");
  const flag =
    `export class Flag {\n  readonly on: boolean;\n` +
    `  constructor(n: number) {\n    this.on = n > 0;\n  }\n` +
    `  /** @ensures{p} forall (n: int ∈ [0, 3)) { new Flag(n).level() >= 0 } */\n` +
    `  level(): number {\n    if (this.on) {\n      return 1;\n    }\n    return 0;\n  }\n}\n`;

  test("a boolean field rides the wire as its keyword and its write is typed at it", () => {
    const { classified, emission } = emit(flag);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const cls = emission.declarations[0];
    assert(cls?.kind === "class");
    expect(cls.fields).toEqual([{ name: "on", type: "boolean" }]);
    expect(cls.ctor.body).toMatchObject([
      { kind: "field-set", field: "on", expr: { kind: "binop", op: ">" } },
    ]);
    expect(cls.methods[0]!.body[0]).toMatchObject({
      kind: "if",
      cond: { kind: "field-read" },
    });
  });

  test("a boolean field on an instance place is a condition, an operand, and an inferred local", () => {
    const { classified, emission } = emit(
      flag +
        `export function pick(f: Flag): number {\n` +
        `  const on = f.on;\n  const off = !on;\n` +
        `  if (f.on && !off) {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toMatchObject({
      kind: "const",
      name: "on",
      type: "boolean",
      init: { kind: "field-read" },
    });
  });

  test("a boolean field is not a number", () => {
    const { classified } = emit(
      flag +
        `/** @ensures{q} forall (n: int ∈ [0, 3)) { count(new Flag(n)) >= 0 } */\n` +
        `export function count(f: Flag): number {\n  return f.on;\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "field 'on' is a boolean, not a number",
    );
  });

  const flagOf =
    `export class Flag {\n  readonly on: boolean;\n` +
    `  constructor(on: boolean) {\n    this.on = on;\n  }\n` +
    `  /** @ensures{reads} forall (f: Flag) { f.level() >= 0 } */\n` +
    `  level(): number {\n    if (this.on) {\n      return 1;\n    }\n    return 0;\n  }\n}\n`;

  test("a boolean constructor parameter rides the wire and heads the class binder", () => {
    const { classified, emission } = emit(flagOf);
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const cls = emission.declarations[0];
    assert(cls?.kind === "class");
    expect(cls.ctor.params).toEqual([{ name: "on", type: "boolean" }]);
    expect(cls.ctor.body).toEqual([
      { kind: "field-set", field: "on", expr: { kind: "id", name: "on" } },
    ]);
    expect(emission.obligations[0]!.payload).toMatchObject({
      kind: "structured",
      binders: [
        {
          name: "f",
          kind: "class",
          className: "Flag",
          ctorParams: [{ name: "on", kind: "boolean" }],
        },
      ],
    });
  });

  test("a construction passes a literal at a boolean slot, in a body and in an atom", () => {
    const { classified, emission } = emit(
      flagOf +
        `/** @ensures{lit} forall (n: int ∈ [0, 10)) { read(n, new Flag(true)) >= 0 } */\n` +
        `export function read(n: number, f: Flag): number {\n` +
        `  if (f.on) {\n    return n;\n  }\n  return 0;\n}\n` +
        `export function off(n: number): number {\n  return read(n, new Flag(false));\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const off = emission.declarations[2];
    assert(off?.kind === "function");
    expect(JSON.stringify(fnBody(off))).toContain(
      '"kind":"new","className":"Flag","args":[{"kind":"bool","value":false}]',
    );
    expect(JSON.stringify(emission.obligations[1]!.payload)).toContain(
      '"kind":"new","className":"Flag","args":[{"kind":"bool","value":true}]',
    );
  });

  test("a defaulted boolean constructor parameter lowers as a defaulted boolean", () => {
    const { classified, emission } = emit(
      `export class Switch {\n  readonly on: boolean;\n` +
        `  constructor(on: boolean = false) {\n    this.on = on;\n  }\n` +
        `  /** @ensures{d} forall (s: Switch) { s.level() >= 0 } */\n` +
        `  level(): number {\n    if (this.on) {\n      return 1;\n    }\n    return 0;\n  }\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const cls = emission.declarations[0];
    assert(cls?.kind === "class");
    expect(cls.ctor.params).toEqual([
      { name: "on", type: ["boolean", "undefined"] },
    ]);
    expect(cls.ctor.body[0]).toMatchObject({
      kind: "const",
      name: "on",
      type: "boolean",
      init: { kind: "cond", else: { kind: "project", tag: "boolean" } },
    });
    expect(emission.obligations[0]!.payload).toMatchObject({
      binders: [
        {
          name: "s",
          kind: "class",
          className: "Switch",
          ctorParams: [{ name: "on", kind: "boolean", defaulted: true }],
        },
      ],
    });
  });

  test("a number is not a boolean constructor argument", () => {
    const { classified } = emit(
      flagOf +
        `/** @ensures{q} forall (n: int ∈ [0, 3)) { g(n) >= 0 } */\n` +
        `export function g(n: number): number {\n  return new Flag(n).level();\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "identifier 'n' is a number, not a boolean",
    );
  });
});

describe("boolean return types (#354)", () => {
  const emit = (src: string) => emitModule(src, "t.ts");

  test("a predicate helper models with a boolean return on the wire", () => {
    const { emission, classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 3)) { isSmall(n) } */\n` +
        `export function isSmall(n: number): boolean {\n  return n < 5;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect(fn.returns).toBe("boolean");
    expect(fnBody(fn)[0]).toEqual({
      kind: "return",
      expr: {
        kind: "binop",
        op: "<",
        left: { kind: "id", name: "n" },
        right: { kind: "num", lit: "5" },
      },
    });
    expect(emission.obligations[0]!.payload).toEqual({
      kind: "structured",
      binders: [{ name: "n", kind: "range", lo: "0", hi: "3" }],
      conclusion: {
        kind: "istrue",
        expr: {
          kind: "call",
          callee: "isSmall",
          args: [{ kind: "id", name: "n" }],
        },
      },
    });
  });

  test("a number function carries no returns field", () => {
    const { emission } = emit(
      `export function f(n: number): number {\n  return n;\n}\n`,
    );
    const fn = emission.declarations[0];
    assert(fn?.kind === "function");
    expect("returns" in fn).toBe(false);
  });

  test("a boolean function must return a boolean", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 3)) { f(n) } */\n` +
        `export function f(n: number): boolean {\n  return n;\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "identifier 'n' is a number, not a boolean",
    );
  });

  test("a call to a boolean callee is a condition, a logical operand, and an equality side", () => {
    const { emission, classified } = emit(
      `export function isSmall(n: number): boolean {\n  return n < 5;\n}\n` +
        `export function clamp(n: number): number {\n` +
        `  if (isSmall(n)) {\n    return 0;\n  }\n` +
        `  if (!isSmall(n) && n > 7) {\n    return 1;\n  }\n` +
        `  if (isSmall(n) === true) {\n    return 2;\n  }\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toMatchObject({
      kind: "if",
      cond: { kind: "call", callee: "isSmall" },
    });
    expect(fnBody(fn)[1]).toMatchObject({
      kind: "if",
      cond: { kind: "binop", op: "&&", left: { kind: "unop", op: "!" } },
    });
    expect(fnBody(fn)[2]).toMatchObject({
      kind: "if",
      cond: {
        kind: "jsval-eq",
        semantics: "strict",
        left: {
          kind: "inject",
          tag: "boolean",
          expr: { kind: "call", callee: "isSmall" },
        },
      },
    });
  });

  test("a call to a boolean callee is not a number", () => {
    const { classified } = emit(
      `export function isSmall(n: number): boolean {\n  return n < 5;\n}\n` +
        `/** @ensures{p} forall (n: int ∈ [0, 3)) { f(n) >= 0 } */\n` +
        `export function f(n: number): number {\n  return isSmall(n);\n}\n`,
    );
    expect(classified).toHaveLength(1);
    expect(classified[0]!.reason).toContain(
      "a call to 'isSmall' yields a boolean, not a number",
    );
  });

  test("a boolean callee inferred into a local binds at boolean", () => {
    const { emission, classified } = emit(
      `export function isSmall(n: number): boolean {\n  return n < 5;\n}\n` +
        `export function f(n: number): number {\n` +
        `  const s = isSmall(n);\n  if (s) {\n    return 0;\n  }\n  return n;\n}\n`,
    );
    expect(classified).toEqual([]);
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fnBody(fn)[0]).toMatchObject({
      kind: "const",
      name: "s",
      type: "boolean",
    });
  });

  test("a boolean call as a conclusion side lowers as a strict-equality island", () => {
    const { emission, classified } = emit(
      `/** @ensures{p} forall (n: int ∈ [0, 3)) { isSmall(n) === true } */\n` +
        `export function isSmall(n: number): boolean {\n  return n < 5;\n}\n`,
    );
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toMatchObject({
      kind: "structured",
      conclusion: {
        kind: "istrue",
        expr: {
          kind: "jsval-eq",
          semantics: "strict",
          left: {
            kind: "inject",
            tag: "boolean",
            expr: { kind: "call", callee: "isSmall" },
          },
          right: {
            kind: "inject",
            tag: "boolean",
            expr: { kind: "bool", value: true },
          },
        },
      },
    });
  });

  test("a method and a getter return boolean, and their reads are conditions", () => {
    const { emission, classified } = emit(
      `export class Gate {\n  readonly level: number;\n` +
        `  constructor(level: number) {\n    this.level = level;\n  }\n` +
        `  get live(): boolean {\n    return this.level > 0;\n  }\n` +
        `  isAbove(k: number): boolean {\n    return this.level > k;\n  }\n` +
        `  pass(n: number): number {\n` +
        `    if (this.live && this.isAbove(n)) {\n      return n;\n    }\n    return 0;\n  }\n}\n` +
        `/** @ensures{p} forall (n: int ∈ [1, 5)) { new Gate(n).live } */\n` +
        `export function passes(n: number): number {\n` +
        `  if (new Gate(n).isAbove(0)) {\n    return n;\n  }\n  return 0;\n}\n`,
    );
    expect(classified).toEqual([]);
    expectValidEmission(emission);
    const cls = emission.declarations[0];
    assert(cls?.kind === "class");
    expect(cls.getters[0]).toMatchObject({ name: "live", returns: "boolean" });
    expect(cls.methods[0]).toMatchObject({
      name: "isAbove",
      returns: "boolean",
    });
    expect("returns" in cls.methods[1]!).toBe(false);
    expect(cls.methods[1]!.body[0]).toMatchObject({
      kind: "if",
      cond: {
        kind: "binop",
        op: "&&",
        left: { kind: "getter-read", name: "live" },
        right: { kind: "method-call", name: "isAbove" },
      },
    });
    expect(emission.obligations[0]!.payload).toMatchObject({
      conclusion: {
        kind: "istrue",
        expr: { kind: "getter-read", name: "live" },
      },
    });
  });

  test("a boolean method call and getter read are not numbers", () => {
    const { classified } = emit(
      `export class Gate {\n  readonly level: number;\n` +
        `  constructor(level: number) {\n    this.level = level;\n  }\n` +
        `  get live(): boolean {\n    return this.level > 0;\n  }\n` +
        `  isAbove(k: number): boolean {\n    return this.level > k;\n  }\n` +
        `  /** @ensures{pa} forall (n: int ∈ [0, 3)) { new Gate(n).a() >= 0 } */\n` +
        `  a(): number {\n    return this.live;\n  }\n` +
        `  /** @ensures{pb} forall (n: int ∈ [0, 3)) { new Gate(n).b() >= 0 } */\n` +
        `  b(): number {\n    return this.isAbove(1);\n  }\n}\n`,
    );
    expect(classified.map((c) => c.reason)).toEqual([
      expect.stringContaining("a member read yields a boolean, not a number"),
      expect.stringContaining("a method call yields a boolean, not a number"),
    ]);
  });
});

describe("residual IR on the wire", () => {
  test("a residual declaration, expression, and discard validate", () => {
    expectValidEmission({
      file: "r.ts",
      declarations: [
        {
          kind: "residual",
          owner: "f",
          site: 1,
          construct: "'Math.log' is not supported",
          params: [{ name: "x", type: "number" }],
          type: "number",
        },
        {
          kind: "function",
          name: "f",
          params: [{ name: "x", type: "number" }],
          source: "",
          noncomputable: true,
          body: [
            {
              kind: "discard",
              expr: {
                kind: "residual",
                owner: "f",
                site: 1,
                args: [{ kind: "id", name: "x" }],
              },
            },
            { kind: "return", expr: { kind: "id", name: "x" } },
          ],
        },
      ],
      obligations: [],
    });
  });

  test("a member's site names its owner and its class carries the flag", () => {
    expectValidEmission({
      file: "r.ts",
      declarations: [
        {
          kind: "residual",
          owner: "C#constructor",
          module: "helper.mts",
          site: 2,
          construct: "'**' is not supported",
          params: [{ name: "self", type: { class: "C" } }],
          type: "boolean",
        },
        {
          kind: "class",
          name: "C",
          fields: [],
          source: "",
          ctor: { params: [], body: [], noncomputable: true },
          getters: [{ name: "g", body: [], noncomputable: true }],
          methods: [{ name: "m", params: [], body: [], noncomputable: true }],
        },
      ],
      obligations: [],
    });
  });

  test("a site numbered below 1 is a schema violation", () => {
    expect(() =>
      expectValidEmission({
        file: "r.ts",
        declarations: [
          {
            kind: "residual",
            owner: "f",
            site: 0,
            construct: "'Math.log' is not supported",
            params: [],
            type: "number",
          },
        ],
        obligations: [],
      }),
    ).toThrow();
  });

  test("an owner spelled outside f or C#member is a schema violation", () => {
    expect(() =>
      expectValidEmission({
        file: "r.ts",
        declarations: [
          {
            kind: "residual",
            owner: "C.m",
            site: 1,
            construct: "'Math.log' is not supported",
            params: [],
            type: "number",
          },
        ],
        obligations: [],
      }),
    ).toThrow();
  });
});

/** The residual declarations of a module's emission, in order. */
function residualsOf(src: string, file = "r.ts") {
  return emitModule(src, file).emission.declarations.filter(
    (d) => d.kind === "residual",
  );
}

describe("residual sites in function bodies", () => {
  test("an unlisted builtin call becomes a residual over the in-scope variables", () => {
    const { emission, classified } = emitModule(fnWith("Math.log(x)"), "r.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations).toEqual([
      {
        kind: "residual",
        owner: "f",
        site: 1,
        construct: "'Math.log' is not supported",
        params: [{ name: "x", type: "number" }],
        type: "number",
      },
      expect.objectContaining({
        kind: "function",
        name: "f",
        body: [
          {
            kind: "return",
            expr: {
              kind: "residual",
              owner: "f",
              site: 1,
              args: [{ kind: "id", name: "x" }],
            },
          },
        ],
      }),
    ]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("the residual is the outermost unmodelable node, modeled context kept", () => {
    const { emission } = emitModule(fnWith("x.y + 1"), "r.ts");
    expect(emission.declarations[0]).toMatchObject({
      kind: "residual",
      site: 1,
      construct: expect.stringMatching(
        /^unmapped TypeScript construct 'PropertyAccessExpression' at 2:\d+$/,
      ),
    });
    const fn = emission.declarations[1];
    assert(fn?.kind === "function");
    expect(fn.body[0]).toMatchObject({
      kind: "return",
      expr: {
        kind: "binop",
        op: "+",
        left: { kind: "residual", site: 1 },
        right: { kind: "num", lit: "1" },
      },
    });
  });

  test("sites number in source order and never share a symbol", () => {
    const rs = residualsOf(fnWith("(x ** 2) + (x ** 2)"));
    expect(rs.map((r) => (r.kind === "residual" ? r.site : 0))).toEqual([1, 2]);
    expect(rs.map((r) => (r.kind === "residual" ? r.construct : ""))).toEqual([
      "'**' is not supported",
      "'**' is not supported",
    ]);
  });

  test("a local bound before the site is one of its arguments", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { const y = x + 1; return Math.log(y); }\n";
    const [r] = residualsOf(src);
    expect(r).toMatchObject({
      params: [
        { name: "x", type: "number" },
        { name: "y", type: "number" },
      ],
    });
  });

  test("a call to a failed declaration is a residual naming the callee's construct", () => {
    const src =
      "declare function probe(n: number): number;\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { if (x < 0) { return probe(x); } return x; }\n";
    const [r] = residualsOf(src);
    expect(r).toMatchObject({
      construct:
        "'probe' could not be modeled: unmapped TypeScript construct 'DeclareKeyword' at 1:1",
    });
  });

  test("a truthiness condition is a boolean residual", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { if (x) { return 1; } return 0; }\n";
    const [r] = residualsOf(src);
    expect(r).toMatchObject({
      type: "boolean",
      construct: expect.stringContaining("Identifier"),
    });
  });

  test("an expression statement is discarded, its residual kept for its effect", () => {
    const src =
      "declare function log(n: number): void;\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { log(x); return x; }\n";
    const decls = emitModule(src, "r.ts").emission.declarations;
    const fn = decls[1];
    assert(fn?.kind === "function");
    expect(fn.body[0]).toMatchObject({
      kind: "discard",
      expr: { kind: "residual", site: 1 },
    });
  });

  test("an expression that assigns inside a residual still fails the declaration", () => {
    const src =
      "declare function probe(n: number): number;\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { let y = x; return probe((y = 2)); }\n";
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        expect.stringContaining(
          "'f' could not be modeled: an assignment at 3:",
        ),
      ],
    ]);
  });

  test("a compound assignment statement still fails the declaration", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { let y = x; y += 1; return y; }\n";
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        expect.stringContaining(
          "'f' could not be modeled: an assignment at 2:",
        ),
      ],
    ]);
  });

  test("a statement outside the slice still fails the declaration", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { for (;;) { return x; } }\n";
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        expect.stringMatching(
          /^'f' could not be modeled: unmapped TypeScript construct 'ForStatement'/,
        ),
      ],
    ]);
  });

  test("a construct-less failure stays an Error, not a residual", () => {
    expect(classifications(fnWith("y")).classified).toEqual([
      ["Error", "'f' could not be modeled: unbound identifier 'y'"],
    ]);
  });

  test("the formula side never residualizes", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= x ** 2 } */\n" +
      "export function f(x: number): number { return x; }\n";
    expect(classifications(src).classified).toEqual([
      ["Inappropriate", "'**' is not supported"],
    ]);
  });
});

describe("residual sites in defaults and members", () => {
  test("a default outside the slice is a residual over the earlier parameters, wrapped", () => {
    const src =
      "export function pow(x: number, y: number = 2 ** 3): number { return x + y; }\n" +
      "/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */\n" +
      "export function g(a: number): number { return pow(a, 1); }\n";
    const { emission, classified } = emitModule(src, "r.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[0]).toMatchObject({
      kind: "residual",
      owner: "pow",
      site: 1,
      construct:
        "parameter 'y' has a default the model cannot evaluate: '**' is not supported",
      params: [{ name: "x", type: "number" }],
      type: "number",
    });
    expect(emission.obligations).toHaveLength(1);
  });

  test("a method's site takes the receiver first", () => {
    const src =
      "export class Pow {\n  #v: number;\n  constructor(v: number) { this.#v = v; }\n" +
      "  /** @ensures{grows} forall (x: number) { 1 <= new Pow(x).square() } */\n" +
      "  square(): number { return this.#v ** 2; }\n}\n";
    const [r] = residualsOf(src);
    expect(r).toMatchObject({
      owner: "Pow#square",
      site: 1,
      construct: "'**' is not supported",
      params: [{ name: "self", type: { class: "Pow" } }],
      type: "number",
    });
    const cls = emitModule(src, "r.ts").emission.declarations[1];
    assert(cls?.kind === "class");
    expect(cls.methods[0]?.body[0]).toMatchObject({
      kind: "return",
      expr: {
        kind: "residual",
        owner: "Pow#square",
        site: 1,
        args: [{ kind: "self" }],
      },
    });
  });

  test("a getter and a constructor own their own sites", () => {
    const src =
      "export class Box {\n  readonly v: number;\n" +
      "  constructor(v: number) { this.v = Math.log(v); }\n" +
      "  /** @ensures{p} forall (x: number) { new Box(x).twice >= 0 } */\n" +
      "  get twice(): number { return Math.log(this.v); }\n}\n";
    expect(
      residualsOf(src).map((r) =>
        r.kind === "residual"
          ? [r.owner, r.site, r.params.map((p) => p.name)]
          : [],
      ),
    ).toEqual([
      ["Box#constructor", 1, ["v"]],
      ["Box#twice", 1, ["self"]],
    ]);
  });

  test("a member failing on its structure still degrades alone", () => {
    const src =
      "export class Pair {\n  #a: number;\n  constructor(a: number) { this.#a = a; }\n" +
      "  /** @ensures{p} forall (x: number) { Object.is(new Pair(x).a, x) } */\n" +
      "  get a(): number { return this.#a; }\n" +
      "  bump(): number { this.#a = 1; return this.#a; }\n}\n";
    const { classified, emission } = emitModule(src, "r.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations.filter((d) => d.kind === "residual")).toEqual(
      [],
    );
  });
});

describe("the noncomputable taint", () => {
  const fnNamed = (src: string, name: string) => {
    const d = emitModule(src, "r.ts").emission.declarations.find(
      (dd) => dd.kind === "function" && dd.name === name,
    );
    assert(d?.kind === "function");
    return d;
  };

  test("an owner with a site is noncomputable; a caller inherits it; a bystander does not", () => {
    const src =
      "export function a(x: number): number { return Math.log(x); }\n" +
      "export function b(x: number): number { return a(x) + 1; }\n" +
      "export function c(x: number): number { return b(x) * 2; }\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { d(x) >= 0 } */\n" +
      "export function d(x: number): number { return x; }\n";
    expect(fnNamed(src, "a").noncomputable).toBe(true);
    expect(fnNamed(src, "b").noncomputable).toBe(true);
    expect(fnNamed(src, "c").noncomputable).toBe(true);
    expect(fnNamed(src, "d")).not.toHaveProperty("noncomputable");
  });

  test("a class taints through its constructor, getters, and methods", () => {
    const src =
      "export class Box {\n  readonly v: number;\n" +
      "  constructor(v: number) { this.v = Math.log(v); }\n" +
      "  get twice(): number { return this.v * 2; }\n" +
      "  plain(): number { return 1; }\n}\n" +
      "/** @ensures{p} forall (x: number) { use(x) >= 0 } */\n" +
      "export function use(x: number): number { return new Box(x).twice; }\n" +
      "export function reads(b: Box): number { return b.twice; }\n" +
      "export function calls(b: Box): number { return b.plain(); }\n";
    const decls = emitModule(src, "r.ts").emission.declarations;
    const cls = decls.find((d) => d.kind === "class");
    assert(cls?.kind === "class");
    expect(cls.ctor.noncomputable).toBe(true);
    expect(cls.getters[0]).not.toHaveProperty("noncomputable");
    expect(cls.methods[0]).not.toHaveProperty("noncomputable");
    expect(fnNamed(src, "use").noncomputable).toBe(true);
    expect(fnNamed(src, "reads")).not.toHaveProperty("noncomputable");
    expect(fnNamed(src, "calls")).not.toHaveProperty("noncomputable");
  });

  test("a getter with its own site taints the functions reading it", () => {
    const src =
      "export class Box {\n  readonly v: number;\n" +
      "  constructor(v: number) { this.v = v; }\n" +
      "  get logged(): number { return Math.log(this.v); }\n}\n" +
      "/** @ensures{p} forall (x: number) { use(x) >= 0 } */\n" +
      "export function use(x: number): number { return new Box(x).logged; }\n";
    const decls = emitModule(src, "r.ts").emission.declarations;
    const cls = decls.find((d) => d.kind === "class");
    assert(cls?.kind === "class");
    expect(cls.ctor).not.toHaveProperty("noncomputable");
    expect(cls.getters[0]?.noncomputable).toBe(true);
    expect(fnNamed(src, "use").noncomputable).toBe(true);
  });

  test("a discarded site taints its owner too", () => {
    const src =
      "declare function log(n: number): void;\n" +
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { log(x); return x; }\n";
    expect(fnNamed(src, "f").noncomputable).toBe(true);
  });

  test("a site in an arm taints through the branch", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
      "export function f(x: number): number { if (x < 0) { return Math.log(x); } return x; }\n";
    expect(fnNamed(src, "f").noncomputable).toBe(true);
  });
});
