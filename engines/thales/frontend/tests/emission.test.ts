import { assert, describe, expect, test } from "vitest";
import * as fs from "node:fs";
import { schemaValidator } from "../../../../tests/helpers/schema-validator.js";
import { emitModule } from "../src/emission.js";

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
        params: ["a", "b"],
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
        "'fetchTotal' could not be modeled: unmapped TypeScript construct 'AwaitExpression' at 8:10",
      ],
      [
        "bumps",
        "Inappropriate",
        "'Counter#bump' could not be modeled: unmapped TypeScript construct 'ClassDeclaration' at 13:3",
      ],
    ]);
  });

  test.each([
    ["engines/thales/tests/fixtures/tracer.ts"],
    ["engines/thales/tests/fixtures/statements.ts"],
    ["engines/thales/tests/fixtures/binders.ts"],
    ["engines/thales/tests/fixtures/degradations.ts"],
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
      "an optional parameter",
      "function f(x?: number): number { return 1; }",
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
      /'Box\.make' could not be modeled: unmapped TypeScript construct 'ClassDeclaration'/,
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
    ["an unparseable atom", "forall (x: int ∈ [0, 5)) { 2x ≡ x }"],
    [
      "an atom that is not valid JavaScript",
      "forall (x: int ∈ [0, 5)) { f(x) is wonderful }",
    ],
    [
      "a half-bounded floor above zero",
      "forall (x: int ∈ [3, ∞)) { f(x) ≡ x }",
    ],
    [
      "a formula the prefix parser rejects",
      "forall (x: int ∈ [0, 5)) (x: int ∈ [0, 5)) { f(x) ≡ x }",
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
  test("unary minus over a non-literal is a unop node", () => {
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) ≡ x } */\n" +
      "export function f(x: number): number { return -x; }\n";
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[0]!.body).toEqual([
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
    expect(emission.declarations[0]!.body).toEqual([
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
    expect(emission.declarations[0]!.body).toEqual([
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

  test("an operator with no model is the engine's Error", () => {
    expect(classifications(fnWith("x & 7"))).toEqual({
      classified: [
        [
          "Error",
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

  test("an engine-failed callee stays the engine's Error", () => {
    const src =
      "export function g(x: number): number { return x & 7; }\n" +
      fnWith("g(x)");
    expect(classifications(src).classified).toEqual([
      [
        "Error",
        "'f' could not be modeled: 'g' has no model: operator '&' has no " +
          "model in this slice",
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
    expect(emission.declarations[0]!.body).toEqual([
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
    expect(emission.declarations[0]!.body).toEqual([
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
    expect(emission.declarations[0]!.body).toHaveLength(1);
  });

  test("an empty arm keeps its statement, an empty else is dropped", () => {
    const src = annotated(
      "export function f(x: number): number { if (x < 0) {} else {} return x; }",
    );
    const { emission, classified } = emitModule(src, "t.ts");
    expect(classified).toEqual([]);
    expect(emission.declarations[0]!.body[0]).toEqual({
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
      "a logical-operator condition",
      "export function f(x: number): number { if (x < 1 && x > 0) { return 1; } return 0; }",
      "BinaryExpression",
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
    expect(emission.declarations[0]!.body).toEqual([
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
    expect(emission.declarations[0]!.body).toEqual([
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

  test("an operator with no model fails property elaboration", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { (x & 7) >= 0 }"))
        .classified,
    ).toEqual([
      [
        "Error",
        "property elaboration failed: operator '&' has no model in this slice",
      ],
    ]);
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
        "unmapped TypeScript construct 'AwaitExpression' at 1:13",
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

  test("a comparison inside an equation side fails property elaboration", () => {
    expect(
      classifications(formulaWith("forall (x: int ∈ [0, 5)) { (x < 1) ≡ x }"))
        .classified,
    ).toEqual([
      [
        "Error",
        "property elaboration failed: operator '<' yields a boolean, not a number",
      ],
    ]);
  });
});

describe("class-valued binders classify Inappropriate (#158)", () => {
  const BOX = "export class Box { constructor(readonly size: number) {} }\n";

  test("a class-valued binder names the construct", () => {
    const src =
      BOX +
      "/** @ensures{p} forall (b: Box) { scale(1) >= 0 } */\n" +
      "export function scale(x: number): number { return x; }\n";
    const { classified, emission } = emitModule(src, "t.ts");
    expect(classified.map((c) => [c.szs, c.reason])).toEqual([
      ["Inappropriate", "class-valued binder 'Box' is not yet modeled"],
    ]);
    expect(emission.obligations).toEqual([]);
    expect(emission.declarations.map((d) => d.name)).toEqual(["scale"]);
  });

  test("the class binder wins over the function's own blocker", () => {
    const src =
      BOX +
      "/** @ensures{p} forall (b: Box) { volume(b) >= 0 } */\n" +
      "export function volume(b: Box): number { return b.size; }\n";
    expect(classifications(src).classified).toEqual([
      ["Inappropriate", "class-valued binder 'Box' is not yet modeled"],
    ]);
  });

  test("the class binder wins over other blockers in the same property", () => {
    const src =
      BOX +
      "/** @ensures{p} forall (b: Box) (s: string) { volume(b) >= 0 ∧ volume(b) >= 0 } */\n" +
      "export function volume(b: Box): number { return b.size; }\n";
    expect(classifications(src).classified).toEqual([
      ["Inappropriate", "class-valued binder 'Box' is not yet modeled"],
    ]);
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
    // The conjunction keeps the body unstructurable, so the clamp never wins.
    const src =
      "/** @ensures{p} forall (x: int ∈ [0, 1000000000000000000000000000000]) { keep(x) >= 0 && keep(x) <= x } */\n" +
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
    expect(emission.declarations[0]!.body[0]).toEqual(
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
          "'Object.is' models numbers only; argument 2 is not a number",
        ),
      }),
    ]);
  });

  test("a bool-valued argument refuses the same way", () => {
    const src = [
      "/** @ensures{p} forall (x: number) { pick(x) === 1 } */",
      "export function pick(x: number): number {",
      "  if (Object.is(x < 1, 0)) {",
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
          "'Object.is' models numbers only; argument 1 is not a number",
        ),
      }),
    ]);
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

  test("a ≢ guard still degrades the property to bare", () => {
    const { emission } = emitModule(
      src("forall (n: int ∈ [0, 2)) { n ≢ 1 -> pick(n) === 1 }"),
      FILE,
    );
    expect(emission.obligations).toEqual([
      expect.objectContaining({ payload: { kind: "bare" } }),
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
