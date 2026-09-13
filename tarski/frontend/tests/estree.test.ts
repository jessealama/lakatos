import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { ParseError, parseScript } from "../src/estree.js";
import { schemaValidator } from "../../../tests/helpers/schema-validator.js";

const validate = schemaValidator(
  new URL("../../../schemas/tarski-estree.schema.json", import.meta.url),
  "ESTree document",
);

const fixture = (name: string): string =>
  fileURLToPath(new URL(`fixtures/${name}`, import.meta.url));

const read = (name: string): string => readFileSync(fixture(name), "utf8");

// The goldens are the seam itself, not a convenience: the Lean decoder is
// written to the same schema, and `tarski/Test/Tarski/fixtures/` holds a
// copy of numeric-loop's that the binary is run on in CI. A diff here is
// a change to the contract between the two languages.
const FIXTURES = [
  "numeric-loop",
  "arithmetic",
  "if-else-block",
  "const-reassign",
  "unsupported-template",
];

describe("parseScript", () => {
  for (const name of FIXTURES) {
    it(`matches the golden document for ${name}.js`, () => {
      const program = parseScript(read(`${name}.js`), `${name}.js`);
      expect(program).toEqual(JSON.parse(read(`${name}.estree.json`)));
    });

    it(`emits a document the schema accepts for ${name}.js`, () => {
      validate(parseScript(read(`${name}.js`), `${name}.js`));
    });
  }

  it("keeps the strict-mode directive as a directive, not an expression", () => {
    const program = parseScript('"use strict";\n1;\n', "d.js");
    expect(program.body[0]).toEqual({
      type: "ExpressionStatement",
      expression: { type: "Literal", value: "use strict", raw: '"use strict"' },
      directive: "use strict",
    });
  });

  // Only the *leading* run of string-literal statements is the prologue;
  // a string statement after real code is an ordinary expression, and
  // strings are outside the slice.
  it("treats a later string statement as an expression, not a directive", () => {
    const program = parseScript('"use strict";\n1;\n"use asm";\n', "d.js");
    expect(program.body[2]).toEqual({
      type: "ExpressionStatement",
      expression: { type: "Unsupported", kind: "StringLiteral" },
    });
  });

  it("replaces a construct outside the slice with its tsc kind, in place", () => {
    const program = parseScript('"use strict";\nlet f = () => 1;\n', "u.js");
    expect(program).toEqual({
      type: "Program",
      sourceType: "script",
      body: [
        {
          type: "ExpressionStatement",
          expression: {
            type: "Literal",
            value: "use strict",
            raw: '"use strict"',
          },
          directive: "use strict",
        },
        {
          type: "VariableDeclaration",
          kind: "let",
          declarations: [
            {
              type: "VariableDeclarator",
              id: { type: "Identifier", name: "f" },
              init: { type: "Unsupported", kind: "ArrowFunction" },
            },
          ],
        },
      ],
    });
  });

  // ESTree has a LogicalExpression the schema does not: the short-circuit
  // operators are out of the slice as nodes, not as operators.
  it("gives the short-circuiting operators no BinaryExpression", () => {
    const program = parseScript('"use strict";\n1 && 2;\n', "l.js");
    expect(program.body[1]).toEqual({
      type: "ExpressionStatement",
      expression: { type: "Unsupported", kind: "BinaryExpression" },
    });
  });

  // The schema admits every assignment and binary operator so the Lean
  // decoder is the one that names what it will not evaluate.
  it("writes an operator outside the slice rather than refusing it", () => {
    const program = parseScript(
      '"use strict";\nlet n = 0;\nn += 1;\nn == 1;\n',
      "o.js",
    );
    expect(program.body[2]).toMatchObject({
      expression: { type: "AssignmentExpression", operator: "+=" },
    });
    expect(program.body[3]).toMatchObject({
      expression: { type: "BinaryExpression", operator: "==" },
    });
    validate(program);
  });

  it("admits var, leaving the refusal to the decoder", () => {
    const program = parseScript('"use strict";\nvar x = 1;\n', "v.js");
    expect(program.body[1]).toMatchObject({
      type: "VariableDeclaration",
      kind: "var",
    });
    validate(program);
  });

  // Parentheses are the parse's business: the tree already says what they
  // grouped, and the schema has no node for them.
  it("drops parentheses", () => {
    const program = parseScript('"use strict";\n(1 + 2) * 3;\n', "p.js");
    expect(program.body[1]).toEqual({
      type: "ExpressionStatement",
      expression: {
        type: "BinaryExpression",
        operator: "*",
        left: {
          type: "BinaryExpression",
          operator: "+",
          left: { type: "Literal", value: 1, raw: "1" },
          right: { type: "Literal", value: 2, raw: "2" },
        },
        right: { type: "Literal", value: 3, raw: "3" },
      },
    });
  });

  // tsc normalizes a literal's value; `raw` keeps what the source wrote,
  // which is what #388 and the bigint slice will need.
  it("keeps a literal's source text beside its value", () => {
    const program = parseScript('"use strict";\n0x1f;\n1_000;\n', "n.js");
    expect(program.body[1]).toMatchObject({
      expression: { type: "Literal", value: 31, raw: "0x1f" },
    });
    expect(program.body[2]).toMatchObject({
      expression: { type: "Literal", value: 1000, raw: "1_000" },
    });
  });

  // `let x;` binds undefined, and the schema's `init` is null for it.
  it("gives a declarator with no initializer a null init", () => {
    const program = parseScript('"use strict";\nlet x;\n', "i.js");
    expect(program.body[1]).toEqual({
      type: "VariableDeclaration",
      kind: "let",
      declarations: [
        {
          type: "VariableDeclarator",
          id: { type: "Identifier", name: "x" },
          init: null,
        },
      ],
    });
  });

  it("leaves a statement outside the slice whole, naming its kind", () => {
    const program = parseScript('"use strict";\nfor (;;) {}\n', "f.js");
    expect(program.body[1]).toEqual({
      type: "Unsupported",
      kind: "ForStatement",
    });
  });

  // A destructuring binding is not an Identifier, and the schema's `id`
  // is one: the declaration leaves the slice as a whole, not piecewise.
  it("refuses a destructuring declaration as one node", () => {
    const program = parseScript(
      '"use strict";\nlet o = 1;\nlet [a, b] = o;\n',
      "d.js",
    );
    expect(program.body[2]).toEqual({
      type: "Unsupported",
      kind: "VariableStatement",
    });
  });

  // A program that does not parse never reaches the evaluator, and
  // parse-phase negatives are not scored: this is the one input the
  // bridge refuses outright.
  it("throws a ParseError naming the position of a syntax error", () => {
    expect(() => parseScript('"use strict";\nlet = ;\n', "bad.js")).toThrow(
      ParseError,
    );
    expect(() => parseScript('"use strict";\nlet = ;\n', "bad.js")).toThrow(
      /bad\.js:2:/,
    );
  });
});

describe("the schema as the seam", () => {
  const ok = JSON.parse(read("numeric-loop.estree.json"));

  it("accepts a document the bridge produced", () => {
    validate(ok);
  });

  // These are the shapes a broken producer sends. The Lean decoder
  // refuses each of them too — `tarski/Test/Tarski/DecodeTest.lean` is the
  // other half — but the schema is what says the document is off-contract
  // before anyone decodes it.
  const rejected: [string, unknown][] = [
    [
      "a BinaryExpression missing its right operand",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ExpressionStatement",
            expression: {
              type: "BinaryExpression",
              operator: "+",
              left: { type: "Literal", value: 1, raw: "1" },
            },
          },
        ],
      },
    ],
    [
      "a node carrying a source position",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ExpressionStatement",
            expression: {
              type: "Literal",
              value: 1,
              raw: "1",
              start: 0,
              end: 1,
            },
          },
        ],
      },
    ],
    ["a module", { type: "Program", sourceType: "module", body: [] }],
    [
      "an Unsupported node with no kind",
      {
        type: "Program",
        sourceType: "script",
        body: [{ type: "Unsupported" }],
      },
    ],
    [
      "a declaration with no declarators",
      {
        type: "Program",
        sourceType: "script",
        body: [{ type: "VariableDeclaration", kind: "let", declarations: [] }],
      },
    ],
  ];

  for (const [what, document] of rejected) {
    it(`rejects ${what}`, () => {
      expect(() => validate(document)).toThrow();
    });
  }
});
