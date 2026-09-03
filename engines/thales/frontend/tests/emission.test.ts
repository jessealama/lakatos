import { assert, describe, expect, test } from "vitest";
import * as fs from "node:fs";
import { schemaValidator } from "../../../../tests/helpers/schema-validator.js";
import {
  type EmitClass,
  type EmitDecl,
  type EmitFunction,
  type EmitStmt,
  emitModule,
} from "../src/emission.js";
import { LemmaError } from "../../../../lemma/src/index.js";

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
    ["engines/thales/tests/fixtures/object-is-tagged.ts"],
    [
      "engines/thales/tests/conformance/theorem/class-binder-equality-guards.ts",
    ],
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
    [
      "engines/thales/tests/fixtures/object-is-tagged.ts",
      "object-is-tagged.emission.json",
    ],
    [
      "engines/thales/tests/conformance/theorem/class-binder-equality-guards.ts",
      "class-binder-equality-guards.emission.json",
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

test("a free function's defaulted parameter still refuses", () => {
  expect(
    classifiedOf("export function f(x: number = 0): number { return x; }"),
  ).toMatch(/unmapped TypeScript construct 'Parameter' at 2:\d+/);
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
    [
      "a blocker in the left operand",
      "function f(x: number): number { return (await g()) + x; }",
      "AwaitExpression",
    ],
    [
      "a blocker in the right operand",
      "function f(x: number): number { return x + (await g()); }",
      "AwaitExpression",
    ],
    [
      "a blocker in a call argument",
      "function f(x: number): number { return f(await g()); }",
      "AwaitExpression",
    ],
  ])("%s classifies its annotation", (_label, decl, construct) => {
    const reason = classifiedOf(decl);
    expect(reason).toMatch(
      /'f' could not be modeled: unmapped TypeScript construct/,
    );
    if (construct !== undefined) expect(reason).toContain(`'${construct}'`);
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
    [
      "a connective outside the chain shape",
      "forall (x: int ∈ [0, 5)) { f(x) >= 0 ∨ f(x) <= 9 }",
    ],
    [
      "an unparseable guard atom",
      "forall (x: int ∈ [0, 5)) { 2x >= 0 -> f(x) >= 0 }",
    ],
    ["a boolean binder", "forall (b: boolean) { f(b) ≡ b }"],
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

const fnWith = (body: string) =>
  `/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n` +
  `export function f(x: number): number { return ${body}; }\n`;

const formulaWith = (formula: string) =>
  `/** @ensures{p} ${formula} */\n` +
  `export function f(x: number): number { return x; }\n`;

describe("body classification parity with the old pipeline", () => {
  test("an overload signature does not shadow its implementation", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number;\n" +
      "export function f(x: number): number { return x; }\n";
    expect(classifications(src)).toEqual({ classified: [], obligations: 1 });
  });

  test("statements after a return are unreachable, as in the old lowering", () => {
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

  test("a body that can run off the end degrades like the old lowering", () => {
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

  test("body pre-scans cover statements after a return", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return g(x); return x.y; }\n";
    const { classified } = classifications(src);
    expect(classified).toEqual([
      [
        "Inappropriate",
        expect.stringMatching(
          /^'f' could not be modeled: unmapped TypeScript construct 'PropertyAccessExpression' at 2:\d+$/,
        ),
      ],
    ]);
  });

  test("** refuses with the spec-fidelity reason", () => {
    expect(classifications(fnWith("x ** 2"))).toEqual({
      classified: [
        [
          "Inappropriate",
          "'f' could not be modeled: '**' is implementation-approximated " +
            "in JavaScript, so any model would certify results a conforming " +
            "engine may disagree with",
        ],
      ],
      obligations: 0,
    });
  });

  test("an operator with no model is outside the model", () => {
    expect(classifications(fnWith("x & 7"))).toEqual({
      classified: [
        [
          "Inappropriate",
          "'f' could not be modeled: operator '&' has no model in this slice",
        ],
      ],
      obligations: 0,
    });
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

  test("a call to a later declaration finds no model, as in the old order", () => {
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

  test("a construct-blocked callee travels its construct to the caller", () => {
    const src =
      "export function g(x: number): number { return x.y; }\n" + fnWith("g(x)");
    expect(classifications(src).classified).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: 'g' could not be modeled: unmapped " +
          "TypeScript construct 'PropertyAccessExpression' at 1:47",
      ],
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
      "a compound assignment",
      "export function f(x: number): number { x += 1; return x; }",
      "ExpressionStatement",
    ],
    [
      "an assignment to a const",
      "export function f(x: number): number { const y = 1; y = 2; return y; }",
      "ExpressionStatement",
    ],
    [
      "a truthiness condition",
      "export function f(x: number): number { if (x) { return 1; } return 0; }",
      "Identifier",
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
    [
      "a call statement",
      "export function f(x: number): number { f(x); return x; }",
      "ExpressionStatement",
    ],
    [
      "an assignment to a property",
      "export function f(x: number): number { x.y = 1; return x; }",
      "ExpressionStatement",
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

  test("an arm's own binding dies with the arm, as in the old lowering", () => {
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

describe("formula classification parity with the old pipeline", () => {
  test("** in a formula is Inappropriate with the bare reason", () => {
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { f(x) ** 2 >= 0 }"),
      ),
    ).toEqual({
      classified: [
        [
          "Inappropriate",
          "'**' is implementation-approximated in JavaScript, so any model " +
            "would certify results a conforming engine may disagree with",
        ],
      ],
      obligations: 0,
    });
  });

  test("** in a guard is Inappropriate with the bare reason", () => {
    expect(
      classifications(
        formulaWith("forall (x: int ∈ [0, 5)) { x ** 2 >= 0 -> f(x) >= 0 }"),
      ),
    ).toEqual({
      classified: [
        [
          "Inappropriate",
          "'**' is implementation-approximated in JavaScript, so any model " +
            "would certify results a conforming engine may disagree with",
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
    ).toEqual([["Inappropriate", "operator '&' has no model in this slice"]]);
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

  test("an unbound identifier fails property elaboration", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { f(x) ≡ q }"))
        .classified,
    ).toEqual([
      ["Error", "property elaboration failed: unbound identifier 'q'"],
    ]);
  });

  test("a number-valued conclusion call fails property elaboration", () => {
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

  test("a numeric conclusion atom fails property elaboration", () => {
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
    "%s as the whole conclusion fails property elaboration",
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
    expect(emission.declarations.map((d) => d.name)).toEqual(["scale"]);
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

  test("a defaulted constructor parameter models, quantified at full arity", () => {
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
          { name: "y", kind: "number" },
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
  test("a caller of a top-level const classifies Inappropriate naming VariableStatement", () => {
    const src = [
      "const double = (x: number): number => x * 2;",
      "/** @ensures{pos} forall (n: int ∈ [0, 4)) { applyDouble(n) >= 0 } */",
      "export function applyDouble(n: number): number {",
      "  return double(n);",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(src, "consts.ts");
    expect(emission.declarations).toEqual([]);
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toBe(
      "'applyDouble' could not be modeled: 'double' could not be modeled: " +
        "unmapped TypeScript construct 'VariableStatement' at 1:7",
    );
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
    const { classified } = emitModule(src, "destructure.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'VariableStatement' at 1:9");
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
    const { classified } = emitModule(src, "imports.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain(
      "unmapped TypeScript construct 'ImportDeclaration' at 1:10",
    );
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
    const { classified } = emitModule(src, "imports.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      ["Inappropriate", expect.stringContaining("'ImportDeclaration' at 1:8")],
      ["Inappropriate", expect.stringContaining("'ImportDeclaration' at 1:19")],
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
    const { classified } = emitModule(src, "imports.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      ["Inappropriate", expect.stringContaining("'ImportDeclaration' at 2:8")],
    ]);
  });
});

describe("unsupported ranges classify NotTried before emission", () => {
  const HUGE =
    "/** @ensures{nonneg} forall (x: int ∈ [0, 1000000000000000000000000000000]) { keep(x) >= 0 } */\n" +
    "export function keep(x: number): number {\n  return x;\n}\n";

  test("a clamped endpoint classifies NotTried with the old reason", () => {
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
    // The disjunction keeps the body unstructurable, so the clamp never wins.
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 1000000000000000000000000000000]) { keep(x) >= 0 ∨ keep(x) <= x } */\n" +
      "export function keep(x: number): number {\n  return x;\n}\n";
    const { classified, emission } = emitModule(src, "huge-bare.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toEqual({ kind: "bare" });
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

  test("a non-numeric argument refuses the declaration naming the call", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { pick(x) === 1 } */",
      "export function pick(x: number): number {",
      '  if (Object.is(x, "zero")) {',
      "    return 0;",
      "  }",
      "  return 1;",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "'Object.is' admits numbers, booleans, union values, " +
            "'undefined', and 'null'; argument 2 is not one",
        ),
      }),
    ]);
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
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("unmapped TypeScript construct"),
      }),
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
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "'NaN' could not be modeled: unmapped TypeScript construct " +
            "'VariableStatement' at 1:7",
        ),
      }),
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
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "'NaN' could not be modeled: unmapped TypeScript construct " +
            "'ImportDeclaration' at 1:10",
        ),
      }),
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

  test("a returned Math.sqrt walks to a math-sqrt node", () => {
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
            expr: { kind: "math-sqrt", arg: { kind: "id", name: "x" } },
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
            left: { kind: "math-sqrt", arg: { kind: "id", name: "n" } },
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

  test("Math.pow keeps the unmapped-construct refusal", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { square(n) >= 0 } */",
      "export function square(x: number): number {",
      "  return Math.pow(x, 2);",
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

  test("a wrong-arity Math.sqrt stays an unmapped construct", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { two(n) >= 0 } */",
      "export function two(x: number): number {",
      "  return Math.sqrt(x, 2);",
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

  test("a refused operator inside the argument is still found", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { f(n) >= 0 } */",
      "export function f(x: number): number {",
      "  return Math.sqrt(x ** 2);",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("**"),
      }),
    ]);
  });
});

describe("builtin member calls model as Float primitives", () => {
  const FILE = "engines/thales/tests/fixtures/tracer.ts"; // any resolvable path; no imports are followed

  test("a returned Math.abs walks to a math-abs node", () => {
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
            expr: { kind: "math-abs", arg: { kind: "id", name: "x" } },
          },
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
            kind: "number-is-finite",
            arg: {
              kind: "call",
              callee: "bump",
              args: [{ kind: "id", name: "n" }],
            },
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
        guards: [{ kind: "number-is-finite", arg: { kind: "id", name: "n" } }],
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
          operand: { kind: "number-is-nan", arg: { kind: "id", name: "x" } },
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
      cond: { kind: "number-is-nan", arg: { kind: "id", name: "x" } },
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
          left: { kind: "number-is-finite", arg: { kind: "id", name: "x" } },
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
          expr: { kind: "number-is-finite", arg: { kind: "id", name: "n" } },
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

  test("Number.parseFloat keeps the unmapped-construct refusal", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { conv(n) >= 0 } */",
      "export function conv(x: number): number {",
      "  return Number.parseFloat(x);",
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

  test("a wrong-arity Number.isFinite stays an unmapped construct", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { two(n) >= 0 } */",
      "export function two(x: number): number {",
      "  if (Number.isFinite(x, 2)) {",
      "    return x;",
      "  }",
      "  return 0;",
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

  test("a parameter named Math shadows the builtin in its own body", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 4)) { mag(n) >= 0 } */",
      "export function mag(Math: number): number {",
      "  return Math.abs(Math);",
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

  test("a refused operator inside a Math.abs argument is still found", () => {
    const src = [
      "/** @ensures{p} forall (n: int ∈ [0, 3)) { f(n) >= 0 } */",
      "export function f(x: number): number {",
      "  return Math.abs(x ** 2);",
      "}",
    ].join("\n");
    const { classified } = emitModule(src, FILE);
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("**"),
      }),
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

  test("a truthiness left operand refuses naming ||", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (x || 1) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason:
          "'pick' could not be modeled: '||' models boolean operands only; " +
          "the left operand is not a boolean (Identifier at 3:7)",
      }),
    ]);
  });

  test("a truthiness right operand refuses naming &&", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (x === 0 && 1) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason:
          "'pick' could not be modeled: '&&' models boolean operands only; " +
          "the right operand is not a boolean (NumericLiteral at 3:18)",
      }),
    ]);
  });

  test("a numeric ! operand refuses naming !", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (!x) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason:
          "'pick' could not be modeled: '!' models boolean operands only; " +
          "the operand is not a boolean (Identifier at 3:8)",
      }),
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

  test("a refused operator inside a logical operand still refuses as itself", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (!(x ** 2 === 0)) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("'**' is implementation-approximated"),
      }),
    ]);
  });

  test("a construct-failed callee inside ! travels with the call", () => {
    const { classified } = emitModule(
      [
        "const g = (x: number): number => x;",
        "/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */",
        "export function pick(x: number): number {",
        "  if (!(g(x) === 0)) {",
        "    return 0;",
        "  }",
        "  return 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("'g' could not be modeled"),
      }),
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

  test("a non-boolean condition refuses the declaration", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
        "export function pick(x: number): number {",
        "  return x ? 0 : 1;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason:
          "'pick' could not be modeled: '?:' models boolean operands only; " +
          "the condition is not a boolean (Identifier at 3:10)",
      }),
    ]);
  });

  test("a refused operator in an arm refuses the declaration", () => {
    const { classified } = emitModule(
      [
        "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
        "export function pick(x: number): number {",
        "  return x < 1 ? 0 : x ** 2;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason:
          "'pick' could not be modeled: '**' is implementation-approximated " +
          "in JavaScript, so any model would certify results a conforming " +
          "engine may disagree with",
      }),
    ]);
  });

  test("a degraded callee in an arm travels to the caller", () => {
    const { classified } = emitModule(
      [
        "export function g(x: number): number {",
        "  return x ** 2;",
        "}",
        "/** @ensures{p} forall (x: number) { Object.is(pick(x), pick(x)) } */",
        "export function pick(x: number): number {",
        "  return x < 1 ? g(x) : 0;",
        "}",
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("'g' could not be modeled: '**'"),
      }),
    ]);
  });

  test("a degraded member in an arm travels to the caller", () => {
    const { classified } = emitModule(
      [
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
      ].join("\n"),
      FILE,
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("'Dep#gone' could not be modeled"),
      }),
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
        fields: ["#v"],
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
    expect(cls.fields).toEqual(["#v"]);
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
    const g = emission.declarations.find((d) => d.name === "g")!;
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
      "a stray semicolon and an opaque constructor statement",
      {
        members: "  ;",
        ctor: "  constructor(v: number) {\n    v;\n    this.#v = v;\n  }",
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
    [
      "a refused operator in the constructor",
      { ctor: "  constructor(v: number) {\n    this.#v = v ** 2;\n  }" },
    ],
  ])("%s degrades the class", (_label, opts) => {
    const { szs, reason } = classClassifiedOf(cls(opts));
    expect(szs).toBe("Inappropriate");
    expect(reason).toMatch(/^'C#v' could not be modeled: /);
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
    [
      "a refused operator in a getter",
      "  get bad(): number {\n    return this.#v ** 2;\n  }",
    ],
    ["a getter that can run off the end", "  get bad(): number {}"],
    [
      "an opaque statement in a getter",
      "  get bad(): number {\n    1;\n    return this.#v;\n  }",
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
      "a refused operator in a new argument",
      "Object.is(new Box(x ** 2).v, x)",
      /'\*\*' is implementation-approximated/,
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
    const pick = emission.declarations.find((d) => d.name === "pick")!;
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
    const { classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(1);
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(/'Wide' could not be modeled/);
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
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods).toEqual([]);
    expect(cls.getters.map((g) => g.name)).toEqual(["v"]);
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
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'bad' could not be modeled");
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

  test("a this-call in a boolean position degrades the caller alone", () => {
    const { emission } = emitModule(
      withPlus(`pick(a: number): number {
    if (this.plus(a)) {
      return 0;
    }
    return 1;
  }`),
      "t.ts",
    );
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods.map((m) => m.name)).toEqual(["plus"]);
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

  test("a refused operator inside a call's receiver or arguments refuses", () => {
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

  test("an opaque construct in a this-call argument refuses the caller", () => {
    const { emission } = emitModule(
      withGone("sum(): number {\n    return this.plus(`a`);\n  }"),
      "t.ts",
    );
    const cls = emission.declarations[0] as EmitClass;
    expect(cls.methods.map((m) => m.name)).toEqual(["plus"]);
  });

  test("a this-call to a degraded sibling travels the sibling's reason", () => {
    const src = withGone(`/** @ensures{p} forall (x: int ∈ [0, 3)) { x < 3 } */
  use(): number {
    return this.gone();
  }`);
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain(
      "'C#gone' could not be modeled: unmapped TypeScript construct 'MethodDeclaration'",
    );
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

  test("a degraded member off a class-typed parameter travels in and out of class", () => {
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
    const { classified } = emitModule(src, "t.ts");
    expect(classified).toHaveLength(2);
    for (const entry of classified) {
      expect(entry.szs).toBe("Inappropriate");
      expect(entry.reason).toContain(
        "'Point#bad' could not be modeled: unmapped TypeScript construct 'ArrayLiteralExpression'",
      );
    }
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
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'Dep#gone' could not be modeled");
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
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toContain(
      "unmapped TypeScript construct 'CallExpression'",
    );
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
  const OMITTED =
    "'P' was constructed with 1 argument(s); parameter 'y' would take its " +
    "default, which the model does not evaluate";

  test("full arity models", () => {
    const { classified, emission } = emitModule(src("new P(a, a)"), "t.ts");
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("an omitted defaulted argument in a property is outside the model", () => {
    const { classified } = emitModule(src("new P(a)"), "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      ["Inappropriate", OMITTED],
    ]);
  });

  test("an omitted defaulted argument in a body travels as the input's refusal", () => {
    const body = `export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { origin(a) >= 0 } */
export function origin(a: number): number {
  return new P(a).x;
}
`;
    const { classified } = emitModule(body, "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      ["Inappropriate", `'origin' could not be modeled: ${OMITTED}`],
    ]);
  });

  test("below the required count is an invariant, not a refusal", () => {
    const { classified } = emitModule(src("new P()"), "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "property elaboration failed: 'P' expects 2 argument(s), got 0",
      ],
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
  const OMITTED =
    "'C#plus' was called with 0 argument(s); parameter 'k' would take its " +
    "default, which the model does not evaluate";

  test("an omitted defaulted argument in a property is outside the model", () => {
    const { classified } = emitModule(
      src.replace("%CALL%", "new C(a).plus()"),
      "t.ts",
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      ["Inappropriate", OMITTED],
    ]);
  });

  test("an omitted defaulted argument in a body travels as the input's refusal", () => {
    const body = `export class C {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  plus(k: number = 1): number {
    return this.x + k;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 } */
export function f(a: number): number {
  return new C(a).plus();
}
`;
    const { classified } = emitModule(body, "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      ["Inappropriate", `'f' could not be modeled: ${OMITTED}`],
    ]);
  });

  test("full arity still models", () => {
    const { classified, emission } = emitModule(
      src.replace("%CALL%", "new C(a).plus(a)"),
      "t.ts",
    );
    expect(classified).toEqual([]);
    expect(emission.obligations).toHaveLength(1);
  });

  test("over the total count is an invariant, not a refusal", () => {
    const { classified } = emitModule(
      src.replace("%CALL%", "new C(a).plus(a, a)"),
      "t.ts",
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Error",
        "property elaboration failed: 'C#plus' expects 1 argument(s), got 2",
      ],
    ]);
  });

  test("a defaulted parameter followed by an optional refuses at zero, models at one", () => {
    const twoParamSrc = `export class D {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { new D(a).plus() >= 0 } */
  plus(k: number = 1, b?: number): number {
    return this.x + k;
  }
}
`;
    const { classified } = emitModule(twoParamSrc, "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'D#plus' was called with 0 argument(s); parameter 'k' would " +
          "take its default, which the model does not evaluate",
      ],
    ]);
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

  test("keeps instance-valued locals refused", () => {
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
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toMatch(
      /yields an instance of 'Point', not a number/,
    );
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
    const { classified } = emitModule(pointWith("", "  return p.#x;"), "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /unmapped TypeScript construct 'PropertyAccessExpression'/,
    );
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
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /unmapped TypeScript construct 'ArrayLiteralExpression'/,
    );
  });

  test("a degraded method called on a class-typed parameter travels", () => {
    const src = pointWith(
      "  loops(): number {\n    for (;;) {}\n    return 1;\n  }",
      "  return p.loops();",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toMatch(
      /'Point#loops' could not be modeled: unmapped TypeScript construct 'ForStatement'/,
    );
  });

  test("a degraded getter read off a class-typed parameter travels", () => {
    const src = pointWith(
      "  get bad(): number {\n    for (;;) {}\n    return 1;\n  }",
      "  return p.bad;",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toMatch(
      /'Point#bad' could not be modeled: unmapped TypeScript construct 'ForStatement'/,
    );
  });

  test("a degraded member inside a receiver call's argument travels", () => {
    const src = pointWith(
      "  loops(): number {\n    for (;;) {}\n    return 1;\n  }\n" +
        "  near(other: Point): number {\n    return other.x;\n  }",
      "  return p.near(new Point(p.loops()));",
    );
    const { classified } = emitModule(src, "t.ts");
    expect(classified[0]!.reason).toMatch(/'Point#loops' could not be modeled/);
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
            expr: { kind: "math-abs", arg: { kind: "id", name: "n" } },
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
      { kind: "number-is-finite", arg: { kind: "id", name: "x" } },
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
    const { classified } = emitModule(src, "let.ts");
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason:
          "'f' could not be modeled: 'factor' could not be modeled: " +
          "unmapped TypeScript construct 'VariableStatement' at 1:5",
      }),
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
    const { classified } = emitModule(src, "string.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain(
      "'label' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement'",
    );
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
    const { emission, classified } = emitModule(src, "annotated.ts");
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({ kind: "constant", name: "wide", lit: "3" }),
    );
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain("'narrow' could not be modeled");
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
      expect.objectContaining({ kind: "constant", name: "floor", lit: "-5" }),
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
    const { emission, classified } = emitModule(src, "mixed.ts");
    expect(emission.declarations[0]).toEqual(
      expect.objectContaining({ kind: "constant", name: "s", lit: "1000" }),
    );
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining("'m' could not be modeled"),
      }),
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
    const { classified } = emitModule(src, "alias-value.ts");
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "'safeMathAbs' aliases 'Math.abs', which is modeled only as a callee",
        ),
      }),
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
    const { classified } = emitModule(src, "alias-arity.ts");
    expect(classified).toEqual([
      expect.objectContaining({
        szs: "Inappropriate",
        reason: expect.stringContaining(
          "unmapped TypeScript construct 'CallExpression'",
        ),
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
    const { classified } = emitModule(src, "shadowed-ns.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain(
      "'safeMathAbs' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement'",
    );
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
    const { classified } = emitModule(src, "unlisted.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain(
      "'safeMathPow' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement'",
    );
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
    const { classified } = emitModule(src, "ambient.ts");
    expect(classified[0]!.szs).toBe("Inappropriate");
    expect(classified[0]!.reason).toContain(
      "'ambient' could not be modeled: unmapped TypeScript construct " +
        "'VariableStatement'",
    );
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
        lit: "1000",
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
    const { classified } = emit(
      `export class C {\n  v: number;\n  constructor(v: number | string) {\n    this.v = 0;\n  }\n}\n` +
        `/** @ensures{p} forall (x: number) { Object.is(get(x), x) } */\n` +
        `export function get(x: number): number {\n  return new C(x).v;\n}\n`,
    );
    expect(classified[0]?.szs).toBe("Inappropriate");
    expect(classified[0]?.reason).toContain(
      "unmapped TypeScript construct 'UnionType'",
    );
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

    const widened = emit(
      `export function wide(v: number | string | boolean): number {\n  return 0;\n}\n` +
        `/** @ensures{p} forall (x: number) { Object.is(narrow(x), 0) } */\n` +
        `export function narrow(v: number | string): number {\n  return wide(v);\n}\n`,
    );
    expect(widened.classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'narrow' could not be modeled: identifier 'v' is a 'number | string' value, " +
          "not a 'number | string | boolean' value; unions flow only between identical spellings",
      ],
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
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), x) } */\n` +
        `export function f(x: number): number {\n  return null;\n}\n`,
    );
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: unmapped TypeScript construct 'NullKeyword' at 3:10",
      ],
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
      const { classified } = emit(
        `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
          `export function f(v: number | string): number {\n  ${body}\n}\n`,
      );
      expect(classified[0]?.szs).toBe("Inappropriate");
      expect(classified[0]?.reason).toContain("'TypeOfExpression'");
    }
    const plain = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(v: number): number {\n` +
        `  if (typeof v === "number") {\n    return v;\n  }\n  return 0;\n}\n`,
    );
    expect(plain.classified[0]?.szs).toBe("Inappropriate");
    expect(plain.classified[0]?.reason).toContain("'TypeOfExpression'");
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
        expr: { kind: "number-is-finite", arg: { kind: "id", name: "x" } },
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
    const eq = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(v: number | string): number {\n` +
        `  if (v === "a") {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(eq.classified[0]?.szs).toBe("Inappropriate");
    expect(eq.classified[0]?.reason).toContain("'StringLiteral'");
    const same = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(v: number | string): number {\n` +
        `  if (Object.is(v, "a")) {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(same.classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'f' could not be modeled: 'Object.is' admits numbers, booleans, " +
          "union values, 'undefined', and 'null'; argument 2 is not one " +
          "(StringLiteral at 3:20)",
      ],
    ]);
  });

  test("without a union operand, a string argument keeps the same refusal", () => {
    const { classified } = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(x: number): number {\n` +
        `  if (Object.is(x, "a")) {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(classified[0]?.reason).toContain(
      "'Object.is' admits numbers, booleans, union values, 'undefined', " +
        "and 'null'; argument 2 is not one",
    );
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
    const call = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function id(v: number | string): number {\n  return 0;\n}\n` +
        `export function f(v: number | string): number {\n` +
        `  if (typeof id(v) === "number") {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(call.classified[0]?.szs).toBe("Inappropriate");
    expect(call.classified[0]?.reason).toContain("'TypeOfExpression'");

    const nonLiteral = emit(
      `/** @ensures{p} forall (x: number) { Object.is(f(x), 0) } */\n` +
        `export function f(v: number | string, s: number): number {\n` +
        `  if (typeof v === s) {\n    return 1;\n  }\n  return 0;\n}\n`,
    );
    expect(nonLiteral.classified[0]?.szs).toBe("Inappropriate");
    expect(nonLiteral.classified[0]?.reason).toContain("'TypeOfExpression'");
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
    const nullArg = emit(
      `/** @ensures{p} forall (x: number) { Object.is(call(x), 0) } */\n` +
        `export function toNum(v: number | string): number {\n  return 0;\n}\n` +
        `export function call(x: number): number {\n  return toNum(null);\n}\n`,
    );
    expect(nullArg.classified.map((c) => [c.szs, c.reason])).toEqual([
      [
        "Inappropriate",
        "'call' could not be modeled: unmapped TypeScript construct 'NullKeyword' at 6:16",
      ],
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
        "'f' could not be modeled: identifier 'v' is a 'number | boolean' value, " +
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
    const { classified } = emit(
      `export class C {\n  v: number;\n  constructor(v: number, w?: number) {\n    this.v = v;\n  }\n}\n` +
        `/** @ensures{p} forall (x: number) { Object.is(get(x), x) } */\n` +
        `export function get(x: number): number {\n  return new C(x, 1).v;\n}\n`,
    );
    expect(classified[0]?.szs).toBe("Inappropriate");
    expect(classified[0]?.reason).toContain(
      "unmapped TypeScript construct 'Parameter' at 3:26",
    );
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
