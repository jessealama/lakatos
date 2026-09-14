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
  "default-param",
  "errors",
  "uncaught",
  "labeled-loops",
  "finally-return",
  "harness-floor",
  "compare-array",
  "print",
  "number-math",
  "for-switch-var",
  "number-conversions",
  "class-box",
  "emitter-classes",
  "hoisting-arguments",
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
    const program = parseScript('"use strict";\ndebugger;\n', "u.js");
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
        { type: "Unsupported", kind: "DebuggerStatement" },
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

  // A class arrives whole: the members carry their kind, their key type,
  // and which side of the class they are on, and the Lean decoder is what
  // refuses the ones outside the slice.
  it("emits a ClassDeclaration with its members", () => {
    const program = parseScript(
      '"use strict";\nclass A {\n  x = 1;\n  #v = 2;\n  static s = 3;\n' +
        "  constructor(v) {}\n  get g() { return 1; }\n  set g(w) {}\n" +
        "  m() {}\n  static sm() {}\n}\n",
      "c.js",
    );
    expect(program.body[1]).toMatchObject({
      type: "ClassDeclaration",
      id: { type: "Identifier", name: "A" },
      superClass: null,
      body: {
        type: "ClassBody",
        body: [
          {
            type: "PropertyDefinition",
            key: { type: "Identifier", name: "x" },
            static: false,
          },
          {
            type: "PropertyDefinition",
            key: { type: "PrivateIdentifier", name: "v" },
            static: false,
          },
          {
            type: "PropertyDefinition",
            key: { type: "Identifier", name: "s" },
            static: true,
          },
          { type: "MethodDefinition", kind: "constructor", static: false },
          { type: "MethodDefinition", kind: "get", static: false },
          { type: "MethodDefinition", kind: "set", static: false },
          { type: "MethodDefinition", kind: "method", static: false },
          { type: "MethodDefinition", kind: "method", static: true },
        ],
      },
    });
    validate(program);
  });

  it("gives a field without an initializer a null value", () => {
    const program = parseScript('"use strict";\nclass A {\n  x;\n}\n', "f.js");
    expect(program.body[1]).toMatchObject({
      body: { body: [{ type: "PropertyDefinition", value: null }] },
    });
    validate(program);
  });

  it("names a class expression, or does not", () => {
    const named = parseScript('"use strict";\nconst C = class N {};\n', "n.js");
    expect(named.body[1]).toMatchObject({
      declarations: [
        {
          init: {
            type: "ClassExpression",
            id: { type: "Identifier", name: "N" },
          },
        },
      ],
    });
    validate(named);
    const anon = parseScript('"use strict";\nconst C = class {};\n', "a.js");
    expect(anon.body[1]).toMatchObject({
      declarations: [{ init: { type: "ClassExpression", id: null } }],
    });
    validate(anon);
  });

  it("carries a heritage clause, including `extends null`", () => {
    const extended = parseScript(
      '"use strict";\nclass A extends B {}\n',
      "e.js",
    );
    expect(extended.body[1]).toMatchObject({
      superClass: { type: "Identifier", name: "B" },
    });
    validate(extended);
    const nulled = parseScript(
      '"use strict";\nclass A extends null {}\n',
      "en.js",
    );
    expect(nulled.body[1]).toMatchObject({
      superClass: { type: "Literal", value: null },
    });
    validate(nulled);
  });

  // `super` is not an expression: it stands in the two positions the
  // schema admits it in and nowhere else.
  it("gives `super` its own node in a call and in a member access", () => {
    const program = parseScript(
      '"use strict";\nclass A extends B {\n  constructor() { super(1); }\n' +
        "  m() { return super.m(); }\n}\n",
      "s.js",
    );
    const body = (program.body[1] as { body: { body: unknown[] } }).body.body;
    expect(body[0]).toMatchObject({
      value: {
        body: {
          body: [
            {
              expression: {
                type: "CallExpression",
                callee: { type: "Super" },
              },
            },
          ],
        },
      },
    });
    expect(body[1]).toMatchObject({
      value: {
        body: {
          body: [
            {
              argument: {
                callee: {
                  type: "MemberExpression",
                  object: { type: "Super" },
                },
              },
            },
          ],
        },
      },
    });
    validate(program);
  });

  it("writes to a private name through a PrivateIdentifier property", () => {
    const program = parseScript(
      '"use strict";\nclass A {\n  #v;\n  constructor() { this.#v = 1; }\n}\n',
      "w.js",
    );
    expect(program.body[1]).toMatchObject({
      body: {
        body: [
          {},
          {
            value: {
              body: {
                body: [
                  {
                    expression: {
                      type: "AssignmentExpression",
                      left: {
                        type: "MemberExpression",
                        property: { type: "PrivateIdentifier", name: "v" },
                      },
                    },
                  },
                ],
              },
            },
          },
        ],
      },
    });
    validate(program);
  });

  // A class member outside the slice stands where it appeared, so the
  // class itself still reaches the Lean decoder — which is also how a
  // private method arrives, for the decoder to refuse by name.
  const CLASS_MEMBERS: [string, string, string][] = [
    ["a static block", "static { }", "ClassStaticBlockDeclaration"],
    ["a computed key", "[k]() {}", "ComputedPropertyName"],
    ["an `accessor` field", "accessor x = 1;", "AccessorKeyword"],
    ["a type annotation", "x: number = 1;", "NumberKeyword"],
    ["an optional marker", "x?;", "QuestionToken"],
    ["a `private` modifier", "private x;", "PrivateKeyword"],
    ["a `readonly` modifier", "readonly x;", "ReadonlyKeyword"],
    ["a parameter property", "constructor(public x) {}", "PublicKeyword"],
    ["a computed field key", "[k] = 1;", "ComputedPropertyName"],
    ["a definite-assignment marker", "x!;", "ExclamationToken"],
    ["a `declare` modifier", "declare x;", "DeclareKeyword"],
  ];

  for (const [what, member, kind] of CLASS_MEMBERS) {
    it(`replaces ${what} in place`, () => {
      const program = parseScript(
        `"use strict";\nclass A {\n  ${member}\n}\n`,
        "m.js",
      );
      expect(JSON.stringify(program)).toContain(`"kind":"${kind}"`);
      validate(program);
    });
  }

  // A string or a numeric key is a member the schema admits and the Lean
  // decoder refuses the numeric one of, so the bridge has to emit both.
  it("emits a string and a numeric member key", () => {
    const program = parseScript(
      '"use strict";\nclass A {\n  "s"() {}\n  1() {}\n  "f" = 1;\n  2 = 2;\n}\n',
      "k.js",
    );
    expect(program.body[1]).toMatchObject({
      body: {
        body: [
          { type: "MethodDefinition", key: { type: "Literal", value: "s" } },
          { type: "MethodDefinition", key: { type: "Literal", value: 1 } },
          { type: "PropertyDefinition", key: { type: "Literal", value: "f" } },
          { type: "PropertyDefinition", key: { type: "Literal", value: 2 } },
        ],
      },
    });
    validate(program);
  });

  // The TypeScript-only parts of a method signature, each refused where
  // it stands rather than taking the method with it.
  const METHOD_SIGNATURES: [string, string, string][] = [
    ["a return type", "m(): number {}", "NumberKeyword"],
    ["an optional marker", "m?() {}", "QuestionToken"],
    ["a type parameter list", "m<T>() {}", "TypeParameter"],
    ["no body at all", "m();", "MethodDeclaration"],
    ["an overload signature", "constructor();", "Constructor"],
  ];

  for (const [what, member, kind] of METHOD_SIGNATURES) {
    it(`replaces a method with ${what} in place`, () => {
      const program = parseScript(
        `"use strict";\nclass A {\n  ${member}\n}\n`,
        "ms.js",
      );
      expect(program.body[1]).toMatchObject({
        body: { body: [{ type: "Unsupported", kind }] },
      });
      validate(program);
    });
  }

  it("keeps a private method, for the Lean decoder to refuse by name", () => {
    const program = parseScript(
      '"use strict";\nclass A {\n  #m() {}\n}\n',
      "pm.js",
    );
    expect(program.body[1]).toMatchObject({
      body: {
        body: [
          {
            type: "MethodDefinition",
            kind: "method",
            key: { type: "PrivateIdentifier", name: "m" },
          },
        ],
      },
    });
    validate(program);
  });

  // These three say something about the class itself, not about one
  // member, so the whole class leaves the slice.
  const WHOLE_CLASS: [string, string, string][] = [
    ["an implements clause", "class A implements B {}", "HeritageClause"],
    ["a type parameter list", "class A<T> {}", "TypeParameter"],
    ["a decorator", "@dec class A {}", "Decorator"],
  ];

  for (const [what, source, kind] of WHOLE_CLASS) {
    it(`refuses a class with ${what} as a whole`, () => {
      const program = parseScript(`"use strict";\n${source}\n`, "wc.js");
      expect(program.body[1]).toEqual({ type: "Unsupported", kind });
      validate(program);
    });
  }

  // A class *expression* leaves the slice as a whole for the same
  // reasons a declaration does.
  it("refuses a class expression with a type parameter list", () => {
    const program = parseScript(
      '"use strict";\nconst C = class<T> {};\n',
      "ce.js",
    );
    expect(program.body[1]).toMatchObject({
      declarations: [{ init: { type: "Unsupported", kind: "TypeParameter" } }],
    });
    validate(program);
  });

  it("drops a stray semicolon between members", () => {
    const program = parseScript(
      '"use strict";\nclass A {\n  ;\n  m() {}\n}\n',
      "sc.js",
    );
    expect(program.body[1]).toMatchObject({
      body: { body: [{ type: "MethodDefinition" }] },
    });
    validate(program);
  });

  // Neither has a node in the slice, so each leaves it whole.
  it("refuses `#x in o` and `new.target`", () => {
    const brand = parseScript(
      '"use strict";\nclass A {\n  #x;\n  static has(o) { return #x in o; }\n}\n',
      "b.js",
    );
    expect(JSON.stringify(brand)).toContain('"kind":"PrivateIdentifier"');
    validate(brand);
    const meta = parseScript(
      '"use strict";\nfunction f() { return new.target; }\n',
      "nt.js",
    );
    expect(JSON.stringify(meta)).toContain('"kind":"MetaProperty"');
    validate(meta);
  });

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

  // `**` is an ordinary `BinaryExpression` in ESTree, and the parser has
  // already resolved its right-associativity, so the bridge has nothing
  // to say about it: `2 ** 3 ** 2` nests to the right.
  it("writes ** as a BinaryExpression operator", () => {
    const program = parseScript('"use strict";\n2 ** 3;\n', "pow.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "BinaryExpression",
        operator: "**",
        left: { type: "Literal", value: 2 },
        right: { type: "Literal", value: 3 },
      },
    });
    validate(program);
  });

  it("nests ** to the right", () => {
    const program = parseScript('"use strict";\n2 ** 3 ** 2;\n', "pow2.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "BinaryExpression",
        operator: "**",
        left: { type: "Literal", value: 2 },
        right: {
          type: "BinaryExpression",
          operator: "**",
          left: { type: "Literal", value: 3 },
          right: { type: "Literal", value: 2 },
        },
      },
    });
    validate(program);
  });

  // A private name is not a property key: it is a name the class's own
  // scope resolves, which is why it has a node of its own rather than
  // being an Identifier.
  it("emits a private-name property", () => {
    const program = parseScript('"use strict";\no.#x;\n', "pr.js");
    expect(program.body[1]).toMatchObject({
      expression: {
        type: "MemberExpression",
        computed: false,
        property: { type: "PrivateIdentifier", name: "x" },
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

  it("writes an array literal's elements in order", () => {
    const program = parseScript(
      '"use strict";\nconst xs = [1, "a", x];\n',
      "a.js",
    );
    expect(program.body[1]).toMatchObject({
      declarations: [
        {
          init: {
            type: "ArrayExpression",
            elements: [
              { type: "Literal", value: 1 },
              { type: "Literal", value: "a" },
              { type: "Identifier", name: "x" },
            ],
          },
        },
      ],
    });
    validate(program);
  });

  // A hole and a spread are each refused where they stand, as an
  // object-literal member and a call argument are, so the literal around
  // them still reaches the Lean decoder.
  it("replaces a hole and a spread element in place", () => {
    const program = parseScript(
      '"use strict";\nconst a = [1, , 2];\nconst b = [...xs, 1];\n',
      "h.js",
    );
    expect(program.body[1]).toMatchObject({
      declarations: [
        {
          init: {
            type: "ArrayExpression",
            elements: [
              { type: "Literal", value: 1 },
              { type: "Unsupported", kind: "OmittedExpression" },
              { type: "Literal", value: 2 },
            ],
          },
        },
      ],
    });
    expect(program.body[2]).toMatchObject({
      declarations: [
        {
          init: {
            type: "ArrayExpression",
            elements: [
              { type: "Unsupported", kind: "SpreadElement" },
              { type: "Literal", value: 1 },
            ],
          },
        },
      ],
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
  // `FunctionDeclaration`. A default is in the slice now, so `Parameter`
  // means a rest parameter.
  it("replaces an out-of-slice parameter in place", () => {
    const program = parseScript(
      '"use strict";\nfunction f(a, b = 1, ...r) {}\nfunction g({ a }) {}\n',
      "pp.js",
    );
    expect(program.body[1]).toMatchObject({
      params: [
        { type: "Identifier", name: "a" },
        {
          type: "AssignmentPattern",
          left: { type: "Identifier", name: "b" },
          right: { type: "Literal", value: 1 },
        },
        { type: "Unsupported", kind: "Parameter" },
      ],
    });
    expect(program.body[2]).toMatchObject({
      params: [{ type: "Unsupported", kind: "ObjectBindingPattern" }],
    });
    validate(program);
  });

  // A binding pattern *with* a default leaves the slice whole: the schema
  // gives an AssignmentPattern an Identifier `left`, so there is nowhere
  // for the pattern to go.
  it("refuses a defaulted binding pattern as one parameter", () => {
    const program = parseScript(
      '"use strict";\nfunction f({ a } = {}) {}\n',
      "dp.js",
    );
    expect(program.body[1]).toMatchObject({
      params: [{ type: "Unsupported", kind: "Parameter" }],
    });
    validate(program);
  });

  // Every function form takes a default, not only a declaration.
  it("gives an arrow and a constructor the same AssignmentPattern", () => {
    const program = parseScript(
      '"use strict";\nconst f = (x = 1) => x;\nclass A { constructor(x = 0) {} }\n',
      "dd.js",
    );
    const pattern = {
      type: "AssignmentPattern",
      left: { type: "Identifier", name: "x" },
    };
    expect(program.body[1]).toMatchObject({
      declarations: [{ init: { params: [pattern] } }],
    });
    expect(program.body[2]).toMatchObject({
      body: { body: [{ value: { params: [pattern] } }] },
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
    const program = parseScript('"use strict";\nwith (o) {}\n', "f.js");
    expect(program.body[1]).toEqual({
      type: "Unsupported",
      kind: "WithStatement",
    });
  });

  // `++` and `--` are the only operators tsc's postfix node carries, and
  // the prefix node shares them with the ordinary unary operators, so the
  // two spellings differ only in `prefix`.
  it.each([
    ["i++", "++", false],
    ["i--", "--", false],
    ["++i", "++", true],
    ["--i", "--", true],
  ])("maps %s to an UpdateExpression", (source, operator, prefix) => {
    const program = parseScript(`"use strict";\n${source};\n`, "u.js");
    expect(program.body[1]).toEqual({
      type: "ExpressionStatement",
      expression: {
        type: "UpdateExpression",
        operator,
        argument: { type: "Identifier", name: "i" },
        prefix,
      },
    });
    validate(program);
  });

  // Every other prefix operator is an ordinary UnaryExpression, which is
  // what keeps `-x` and `--x` apart.
  it("leaves the other prefix operators a UnaryExpression", () => {
    const program = parseScript('"use strict";\n-i;\n', "n.js");
    expect(program.body[1]).toMatchObject({
      expression: { type: "UnaryExpression", operator: "-", prefix: true },
    });
  });

  // tsc gives `void` a node of its own, as it does `typeof`; ESTree
  // spells both as unary operators.
  it("maps void to a UnaryExpression", () => {
    const program = parseScript('"use strict";\nvoid x;\n', "v.js");
    expect(program.body[1]).toEqual({
      type: "ExpressionStatement",
      expression: {
        type: "UnaryExpression",
        operator: "void",
        argument: { type: "Identifier", name: "x" },
        prefix: true,
      },
    });
    validate(program);
  });

  it("gives an empty for head three nulls and an EmptyStatement body", () => {
    const program = parseScript('"use strict";\nfor (;;) ;\n', "e.js");
    expect(program.body[1]).toEqual({
      type: "ForStatement",
      init: null,
      test: null,
      update: null,
      body: { type: "EmptyStatement" },
    });
    validate(program);
  });

  it("keeps every declarator of a for head", () => {
    const program = parseScript(
      '"use strict";\nfor (var i = 0, j = 1; i < j; i++) {}\n',
      "h.js",
    );
    expect(program.body[1]).toMatchObject({
      type: "ForStatement",
      init: {
        type: "VariableDeclaration",
        kind: "var",
        declarations: [
          { id: { type: "Identifier", name: "i" } },
          { id: { type: "Identifier", name: "j" } },
        ],
      },
    });
    validate(program);
  });

  // A pattern in the head is refused where it stands, so the loop around
  // it still reaches the Lean decoder and the refusal names the pattern.
  it("refuses a destructuring for head in place", () => {
    const program = parseScript(
      '"use strict";\nconst xs = [1];\nfor (const [a] = xs; ; ) {}\n',
      "p.js",
    );
    expect(program.body[2]).toMatchObject({
      type: "ForStatement",
      init: { type: "Unsupported", kind: "VariableDeclarationList" },
    });
    validate(program);
  });

  // An expression head is not a declaration, and carries no `kind`.
  it("takes an expression for head as an expression", () => {
    const program = parseScript('"use strict";\nfor (i = 0; ; ) {}\n', "x.js");
    expect(program.body[1]).toMatchObject({
      type: "ForStatement",
      init: { type: "AssignmentExpression", operator: "=" },
    });
    validate(program);
  });

  it("preserves clause order, default included", () => {
    const program = parseScript(
      '"use strict";\nswitch (x) { case 1: a(); default: b(); case 2: break; }\n',
      "s.js",
    );
    expect(program.body[1]).toMatchObject({
      type: "SwitchStatement",
      discriminant: { type: "Identifier", name: "x" },
      cases: [
        { type: "SwitchCase", test: { type: "Literal", value: 1 } },
        { type: "SwitchCase", test: null },
        { type: "SwitchCase", test: { type: "Literal", value: 2 } },
      ],
    });
    validate(program);
  });

  // The two loop forms that are not in the slice, each named by its own
  // tsc kind so the runner's histogram says which one to land next.
  it.each([
    ["for (k in o) ;", "ForInStatement"],
    ["for (x of xs) ;", "ForOfStatement"],
  ])("refuses %s as %s", (source, kind) => {
    const program = parseScript(`"use strict";\n${source}\n`, "l.js");
    expect(program.body[1]).toEqual({ type: "Unsupported", kind });
    validate(program);
  });

  // `do`/`while` is in the slice: the body comes first, as it does in
  // the source.
  it("emits a DoWhileStatement with the body ahead of the test", () => {
    const program = parseScript(
      '"use strict";\ndo { x++; } while (x < 3);\n',
      "d.js",
    );
    expect(program.body[1]).toMatchObject({
      type: "DoWhileStatement",
      body: { type: "BlockStatement" },
      test: { type: "BinaryExpression", operator: "<" },
    });
    validate(program);
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
      "an ArrayExpression with no elements field",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ExpressionStatement",
            expression: { type: "ArrayExpression" },
          },
        ],
      },
    ],
    [
      "a MethodDefinition with a computed key",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ClassDeclaration",
            id: { type: "Identifier", name: "A" },
            superClass: null,
            body: {
              type: "ClassBody",
              body: [
                {
                  type: "MethodDefinition",
                  key: { type: "Identifier", name: "m" },
                  value: {
                    type: "FunctionExpression",
                    id: null,
                    params: [],
                    body: { type: "BlockStatement", body: [] },
                    async: false,
                    generator: false,
                  },
                  kind: "method",
                  computed: true,
                  static: false,
                },
              ],
            },
          },
        ],
      },
    ],
    [
      "a Super as a call argument",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ExpressionStatement",
            expression: {
              type: "CallExpression",
              callee: { type: "Identifier", name: "f" },
              arguments: [{ type: "Super" }],
            },
          },
        ],
      },
    ],
    [
      "a PrivateIdentifier as a CallExpression callee",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "ExpressionStatement",
            expression: {
              type: "CallExpression",
              callee: { type: "PrivateIdentifier", name: "x" },
              arguments: [],
            },
          },
        ],
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
    [
      "an AssignmentPattern whose left is a MemberExpression",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "FunctionDeclaration",
            id: { type: "Identifier", name: "f" },
            params: [
              {
                type: "AssignmentPattern",
                left: {
                  type: "MemberExpression",
                  object: { type: "Identifier", name: "o" },
                  property: { type: "Identifier", name: "x" },
                  computed: false,
                },
                right: { type: "Literal", value: 1, raw: "1" },
              },
            ],
            body: { type: "BlockStatement", body: [] },
            async: false,
            generator: false,
          },
        ],
      },
    ],
    [
      "an AssignmentPattern as a Statement",
      {
        type: "Program",
        sourceType: "script",
        body: [
          {
            type: "AssignmentPattern",
            left: { type: "Identifier", name: "x" },
            right: { type: "Literal", value: 1, raw: "1" },
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
