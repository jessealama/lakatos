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
  "counter",
  "factorial",
  "prototype-chain",
  "arrow-this",
  "unsupported-default-param",
  "errors",
  "uncaught",
  "labeled-loops",
  "finally-return",
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
  // a string statement after real code is an ordinary expression, and it
  // carries no `directive`, which is what the Lean side reads.
  it("treats a later string statement as an expression, not a directive", () => {
    const program = parseScript('"use strict";\n1;\n"use asm";\n', "d.js");
    expect(program.body[2]).toEqual({
      type: "ExpressionStatement",
      expression: { type: "Literal", value: "use asm", raw: '"use asm"' },
    });
  });

  it("replaces a construct outside the slice with its tsc kind, in place", () => {
    const program = parseScript('"use strict";\nclass A {}\n', "u.js");
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
        { type: "Unsupported", kind: "ClassDeclaration" },
      ],
    });
  });

  // ESTree gives the short-circuiting operators a node of their own,
  // because they do not evaluate both operands.
  it("gives the short-circuiting operators a LogicalExpression", () => {
    const program = parseScript('"use strict";\n1 && 2;\n1 ?? 2;\n', "l.js");
    expect(program.body[1]).toEqual({
      type: "ExpressionStatement",
      expression: {
        type: "LogicalExpression",
        operator: "&&",
        left: { type: "Literal", value: 1, raw: "1" },
        right: { type: "Literal", value: 2, raw: "2" },
      },
    });
    // `??` is written out with them and refused by the Lean decoder.
    expect(program.body[2]).toMatchObject({
      expression: { type: "LogicalExpression", operator: "??" },
    });
    validate(program);
  });

  it("gives typeof the unary operator ESTree spells it with", () => {
    const program = parseScript('"use strict";\ntypeof x;\n', "t.js");
    expect(program.body[1]).toEqual({
      type: "ExpressionStatement",
      expression: {
        type: "UnaryExpression",
        operator: "typeof",
        argument: { type: "Identifier", name: "x" },
        prefix: true,
      },
    });
  });

  it("distinguishes a dot access from a bracket access by computed", () => {
    const program = parseScript('"use strict";\no.x;\no[k];\n', "m.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "MemberExpression",
        computed: false,
        property: { type: "Identifier", name: "x" },
      },
    });
    expect(program.body[2]).toMatchObject({
      expression: {
        type: "MemberExpression",
        computed: true,
        property: { type: "Identifier", name: "k" },
      },
    });
    validate(program);
  });

  it("writes a member target as the assignment's left", () => {
    const program = parseScript('"use strict";\no.x = 1;\n', "a.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "AssignmentExpression",
        operator: "=",
        left: { type: "MemberExpression", computed: false },
      },
    });
    validate(program);
  });

  it("gives new with no argument list an empty arguments", () => {
    const program = parseScript('"use strict";\nnew F;\nnew F(1);\n', "c.js");
    expect(program.body[1]).toMatchObject({
      expression: { type: "NewExpression", arguments: [] },
    });
    expect(program.body[2]).toMatchObject({
      expression: {
        type: "NewExpression",
        arguments: [{ type: "Literal", value: 1, raw: "1" }],
      },
    });
    validate(program);
  });

  // `async` and `generator` are real syntax whose semantics the epic does
  // not model: the bridge writes the flags and the Lean decoder names
  // them, as it does for `var`.
  it("emits the async and generator flags rather than refusing them", () => {
    const program = parseScript(
      '"use strict";\nasync function f() {}\nfunction* g() {}\n',
      "g.js",
    );
    expect(program.body[1]).toMatchObject({
      type: "FunctionDeclaration",
      async: true,
      generator: false,
    });
    expect(program.body[2]).toMatchObject({
      type: "FunctionDeclaration",
      async: false,
      generator: true,
    });
    validate(program);
  });

  it("marks a concise arrow body with expression: true", () => {
    const program = parseScript(
      '"use strict";\nconst f = (x) => x;\nconst g = () => {};\n',
      "ar.js",
    );
    expect(program.body[1]).toMatchObject({
      declarations: [
        {
          init: {
            type: "ArrowFunctionExpression",
            expression: true,
            body: { type: "Identifier", name: "x" },
          },
        },
      ],
    });
    expect(program.body[2]).toMatchObject({
      declarations: [
        {
          init: {
            type: "ArrowFunctionExpression",
            expression: false,
            body: { type: "BlockStatement", body: [] },
          },
        },
      ],
    });
    validate(program);
  });

  // An object-literal member outside the slice stands where it appeared,
  // so the literal itself still reaches the Lean decoder.
  const MEMBERS: [string, string][] = [
    ["a shorthand property", "{ a }"],
    ["a computed key", "{ [k]: 1 }"],
    ["a method", "{ m() {} }"],
    ["a getter", "{ get m() { return 1; } }"],
    ["a spread", "{ ...o }"],
  ];
  const MEMBER_KINDS: Record<string, string> = {
    "{ a }": "ShorthandPropertyAssignment",
    "{ [k]: 1 }": "ComputedPropertyName",
    "{ m() {} }": "MethodDeclaration",
    "{ get m() { return 1; } }": "GetAccessor",
    "{ ...o }": "SpreadAssignment",
  };

  for (const [what, source] of MEMBERS) {
    it(`replaces ${what} in place`, () => {
      const program = parseScript(
        `"use strict";\nconst o = ${source};\n`,
        "p.js",
      );
      expect(program.body[1]).toMatchObject({
        declarations: [
          {
            init: {
              type: "ObjectExpression",
              properties: [{ type: "Unsupported", kind: MEMBER_KINDS[source] }],
            },
          },
        ],
      });
      validate(program);
    });
  }

  it("gives a throw its argument", () => {
    const program = parseScript('"use strict";\nthrow e;\n', "th.js");
    expect(program.body[1]).toEqual({
      type: "ThrowStatement",
      argument: { type: "Identifier", name: "e" },
    });
    validate(program);
  });

  it("writes all three parts of a try", () => {
    const program = parseScript(
      '"use strict";\ntry { } catch (e) { } finally { }\n',
      "t.js",
    );
    expect(program.body[1]).toEqual({
      type: "TryStatement",
      block: { type: "BlockStatement", body: [] },
      handler: {
        type: "CatchClause",
        param: { type: "Identifier", name: "e" },
        body: { type: "BlockStatement", body: [] },
      },
      finalizer: { type: "BlockStatement", body: [] },
    });
    validate(program);
  });

  // The optional-binding form and the clause-less form: each absent part
  // is null rather than missing, because the Lean decoder reads a field.
  it("gives an absent catch binding, catch clause, or finalizer null", () => {
    const program = parseScript(
      '"use strict";\ntry { } catch { }\ntry { } finally { }\n',
      "t2.js",
    );
    expect(program.body[1]).toMatchObject({
      handler: { type: "CatchClause", param: null },
      finalizer: null,
    });
    expect(program.body[2]).toMatchObject({
      handler: null,
      finalizer: { type: "BlockStatement", body: [] },
    });
    validate(program);
  });

  // A destructuring catch binding is refused in place, so the clause —
  // and the `try` around it — survives, as an out-of-slice parameter
  // leaves its function standing.
  it("replaces a destructuring catch binding in place", () => {
    const program = parseScript(
      '"use strict";\ntry { } catch ({ message }) { }\n',
      "t3.js",
    );
    expect(program.body[1]).toMatchObject({
      type: "TryStatement",
      handler: {
        type: "CatchClause",
        param: { type: "Unsupported", kind: "ObjectBindingPattern" },
      },
    });
    validate(program);
  });

  it("gives a labelled loop its label and both jumps theirs", () => {
    const program = parseScript(
      '"use strict";\na: while (x) { break a; continue a; }\n',
      "lb.js",
    );
    expect(program.body[1]).toEqual({
      type: "LabeledStatement",
      label: { type: "Identifier", name: "a" },
      body: {
        type: "WhileStatement",
        test: { type: "Identifier", name: "x" },
        body: {
          type: "BlockStatement",
          body: [
            {
              type: "BreakStatement",
              label: { type: "Identifier", name: "a" },
            },
            {
              type: "ContinueStatement",
              label: { type: "Identifier", name: "a" },
            },
          ],
        },
      },
    });
    validate(program);
  });

  // `break` outside a loop is a checker error in tsc, not a parse error,
  // so it reaches the bridge and the evaluator says what it means.
  it("gives an unlabelled break a null label", () => {
    const program = parseScript('"use strict";\nbreak;\ncontinue;\n', "br.js");
    expect(program.body[1]).toEqual({ type: "BreakStatement", label: null });
    expect(program.body[2]).toEqual({ type: "ContinueStatement", label: null });
    validate(program);
  });

  it("writes instanceof as a BinaryExpression operator", () => {
    const program = parseScript('"use strict";\nx instanceof Y;\n', "io.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "BinaryExpression",
        operator: "instanceof",
        left: { type: "Identifier", name: "x" },
        right: { type: "Identifier", name: "Y" },
      },
    });
    validate(program);
  });

  // A private name is a property the slice does not read, and it is the
  // property that leaves the slice, not the access.
  it("replaces a private-name property in place", () => {
    const program = parseScript('"use strict";\no.#x;\n', "pr.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "MemberExpression",
        computed: false,
        property: { type: "Unsupported", kind: "PrivateIdentifier" },
      },
    });
    validate(program);
  });

  it("gives a bare return a null argument", () => {
    const program = parseScript(
      '"use strict";\nfunction f() { return; }\n',
      "r.js",
    );
    expect(program.body[1]).toMatchObject({
      body: {
        type: "BlockStatement",
        body: [{ type: "ReturnStatement", argument: null }],
      },
    });
    validate(program);
  });

  it("keeps a string or numeric object key as the literal it is", () => {
    const program = parseScript(
      '"use strict";\nconst o = { "a b": 1, 2: 3 };\n',
      "k.js",
    );
    expect(program.body[1]).toMatchObject({
      declarations: [
        {
          init: {
            type: "ObjectExpression",
            properties: [
              { key: { type: "Literal", value: "a b", raw: '"a b"' } },
              { key: { type: "Literal", value: 2, raw: "2" } },
            ],
          },
        },
      ],
    });
    validate(program);
  });

  // A named function expression binds its own name inside itself; the
  // schema's `id` is where that name arrives.
  it("keeps a function expression's own name", () => {
    const program = parseScript(
      '"use strict";\nconst f = function fac(n) { return n; };\n',
      "fe.js",
    );
    expect(program.body[1]).toMatchObject({
      declarations: [
        {
          init: {
            type: "FunctionExpression",
            id: { type: "Identifier", name: "fac" },
          },
        },
      ],
    });
    validate(program);
  });

  // An optional chain short-circuits the whole chain, which is semantics
  // of its own: the access leaves the slice as a whole.
  it("refuses an optional chain as one node", () => {
    const program = parseScript(
      '"use strict";\na?.b;\nf?.();\na?.[b];\n',
      "q.js",
    );
    expect(program.body[1]).toMatchObject({
      expression: { type: "Unsupported", kind: "PropertyAccessExpression" },
    });
    expect(program.body[2]).toMatchObject({
      expression: { type: "Unsupported", kind: "CallExpression" },
    });
    expect(program.body[3]).toMatchObject({
      expression: { type: "Unsupported", kind: "ElementAccessExpression" },
    });
    validate(program);
  });

  it("replaces a spread argument in place, keeping the call", () => {
    const program = parseScript('"use strict";\nf(...xs);\n', "s.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "CallExpression",
        arguments: [{ type: "Unsupported", kind: "SpreadElement" }],
      },
    });
    validate(program);
  });

  // A parameter outside the slice is refused alone: the function node
  // survives, which is what lets the decoder say `Parameter` rather than
  // `FunctionDeclaration`.
  it("replaces an out-of-slice parameter in place", () => {
    const program = parseScript(
      '"use strict";\nfunction f(a, b = 1, ...r) {}\nfunction g({ a }) {}\n',
      "pp.js",
    );
    expect(program.body[1]).toMatchObject({
      params: [
        { type: "Identifier", name: "a" },
        { type: "Unsupported", kind: "Parameter" },
        { type: "Unsupported", kind: "Parameter" },
      ],
    });
    expect(program.body[2]).toMatchObject({
      params: [{ type: "Unsupported", kind: "ObjectBindingPattern" }],
    });
    validate(program);
  });

  // A template with no substitutions is a string, but not a
  // StringLiteral: it stays outside the slice.
  it("keeps a substitution-free template outside the slice", () => {
    const program = parseScript('"use strict";\n`x`;\n', "tp.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "Unsupported",
        kind: "NoSubstitutionTemplateLiteral",
      },
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
    [
      "a Property with a computed key",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ExpressionStatement",
            expression: {
              type: "ObjectExpression",
              properties: [
                {
                  type: "Property",
                  key: { type: "Identifier", name: "a" },
                  value: { type: "Literal", value: 1, raw: "1" },
                  kind: "init",
                  computed: true,
                  shorthand: false,
                  method: false,
                },
              ],
            },
          },
        ],
      },
    ],
    [
      "a TryStatement missing handler",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "TryStatement",
            block: { type: "BlockStatement", body: [] },
            finalizer: { type: "BlockStatement", body: [] },
          },
        ],
      },
    ],
    [
      "a CatchClause whose param is a string",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "TryStatement",
            block: { type: "BlockStatement", body: [] },
            handler: {
              type: "CatchClause",
              param: "e",
              body: { type: "BlockStatement", body: [] },
            },
            finalizer: null,
          },
        ],
      },
    ],
    [
      "a BreakStatement missing label",
      {
        type: "Program",
        sourceType: "script",
        body: [{ type: "BreakStatement" }],
      },
    ],
    [
      "a CallExpression with no arguments field",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ExpressionStatement",
            expression: {
              type: "CallExpression",
              callee: { type: "Identifier", name: "f" },
            },
          },
        ],
      },
    ],
  ];

  for (const [what, document] of rejected) {
    it(`rejects ${what}`, () => {
      expect(() => validate(document)).toThrow();
    });
  }
});
