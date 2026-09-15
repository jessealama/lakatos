// The parser bridge: a JavaScript file in, an ESTree-shaped document out,
// exactly as `schemas/tarski-estree.schema.json` fixes it. The Lean side
// decodes that document; the schema is the seam, and neither language
// parses JavaScript twice.
//
// A construct outside tarski's slice is not an error here. It is replaced
// in place by an `Unsupported` node carrying the tsc kind it stood for, so
// the document still validates and the Lean decoder is the single place
// that refuses a program and names what it refused. Only a syntax error
// stops the bridge: a program that does not parse never reaches the
// evaluator at all, and parse-phase negatives are not scored.

import ts from "typescript";

/** The proper name of each SyntaxKind: plain reverse lookup can land on a
 * First-/Last- range marker sharing the same value, so pick the first
 * non-marker name per value. Copied rather than imported from thales —
 * tarski may not depend on an engine. */
const KIND_NAMES = new Map<number, string>();
for (const [name, value] of Object.entries(ts.SyntaxKind)) {
  if (
    typeof value === "number" &&
    !/^(First|Last)[A-Z]/.test(name) &&
    !KIND_NAMES.has(value)
  ) {
    KIND_NAMES.set(value, name);
  }
}

function kindName(kind: ts.SyntaxKind): string {
  return KIND_NAMES.get(kind)!;
}

/** A source file that does not parse. */
export class ParseError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "ParseError";
  }
}

export interface Unsupported {
  type: "Unsupported";
  kind: string;
}

export interface Identifier {
  type: "Identifier";
  name: string;
}

export interface Literal {
  type: "Literal";
  value: number | boolean | string | null;
  raw: string;
}

/** A target with a default. ESTree spells `function f(x = 1) {}`'s
 * parameter this way, and `const [a = 1] = xs`'s element and
 * `({ a = 1 } = o)`'s property too; `left` is the target and `right` the
 * initializer, which runs only when the value is `undefined`. */
export interface AssignmentPattern {
  type: "AssignmentPattern";
  left: Pattern;
  right: Expression;
}

/** `...x` in an array literal, an argument list, or an object literal.
 * In a *pattern* the same source is a `RestElement`. */
export interface SpreadElement {
  type: "SpreadElement";
  argument: Expression;
}

/** `...x` in a pattern: a parameter list's last parameter, an array
 * pattern's last element, or an object pattern's last property. The
 * grammar allows a pattern argument only in the first two. */
export interface RestElement {
  type: "RestElement";
  argument: Pattern;
}

/** `[a, , ...rest]` as a binding or assignment target. A `null` element
 * is an elision. */
export interface ArrayPattern {
  type: "ArrayPattern";
  elements: (Pattern | RestElement | null)[];
}

/** `{ a, b: c = 1, ...rest }` as a binding or assignment target. */
export interface ObjectPattern {
  type: "ObjectPattern";
  properties: (PatternProperty | RestElement)[];
}

/** One property of an `ObjectPattern`: a `Property` whose `value` is a
 * pattern. `shorthand` is true for `{ a }` and for `{ a = 1 }`, whose
 * `value` is then an `AssignmentPattern` over the same name. */
export interface PatternProperty {
  type: "Property";
  key: Expression;
  value: Pattern;
  kind: "init";
  computed: boolean;
  shorthand: boolean;
  method: false;
}

/** What a binding or an assignment pattern may be written with. A
 * `MemberExpression` leaf is legal only in an assignment pattern, which
 * the Lean decoder is what enforces. */
export type Pattern =
  | Identifier
  | MemberExpression
  | ArrayPattern
  | ObjectPattern
  | AssignmentPattern
  | Unsupported;

export interface UnaryExpression {
  type: "UnaryExpression";
  operator: string;
  argument: Expression;
  prefix: true;
}

export interface UpdateExpression {
  type: "UpdateExpression";
  operator: "++" | "--";
  argument: Expression;
  prefix: boolean;
}

export interface BinaryExpression {
  type: "BinaryExpression";
  operator: string;
  left: Expression;
  right: Expression;
}

export interface LogicalExpression {
  type: "LogicalExpression";
  operator: string;
  left: Expression;
  right: Expression;
}

export interface ThisExpression {
  type: "ThisExpression";
}

/** `super`, which is not an expression: it may only be the object of a
 * member access or the callee of a call, and the schema puts it in those
 * two positions and nowhere else. */
export interface Super {
  type: "Super";
}

/** A `#name`, which is not an expression either: it may only be a
 * member access's property. `name` is ESTree's — without the `#`. */
export interface PrivateIdentifier {
  type: "PrivateIdentifier";
  name: string;
}

export interface MemberExpression {
  type: "MemberExpression";
  object: Expression | Super;
  property: Expression | PrivateIdentifier;
  computed: boolean;
}

export interface CallExpression {
  type: "CallExpression";
  callee: Expression | Super;
  arguments: (Expression | SpreadElement)[];
}

export interface NewExpression {
  type: "NewExpression";
  callee: Expression;
  arguments: (Expression | SpreadElement)[];
}

/** One member of an object literal. `key` is an `Identifier` or a string
 * or numeric `Literal` unless `computed`, in which case it is any
 * expression. `value` is a `FunctionExpression` when `kind` is `"get"` or
 * `"set"` or when `method` is true; a shorthand's `value` is its own
 * `Identifier`. Spread is a `SpreadElement` among the properties. */
export interface Property {
  type: "Property";
  key: Expression;
  value: Expression;
  kind: "init" | "get" | "set";
  computed: boolean;
  shorthand: boolean;
  method: boolean;
}

/** One piece of a template's text. `cooked` is null only under a tag:
 * an escape the cooked grammar refuses is a parse error in an untagged
 * template, and the bridge refuses a program that does not parse. `raw`
 * is the TRV, so its line terminators are normalized to `\n`. */
export interface TemplateElement {
  type: "TemplateElement";
  value: { cooked: string | null; raw: string };
  tail: boolean;
}

/** A template literal: one more quasi than there are expressions, so a
 * template with no substitutions is one quasi and no expressions. */
export interface TemplateLiteral {
  type: "TemplateLiteral";
  quasis: TemplateElement[];
  expressions: Expression[];
}

export interface TaggedTemplateExpression {
  type: "TaggedTemplateExpression";
  tag: Expression;
  quasi: TemplateLiteral;
}

/** An array literal. A `null` element is an elision — the source's
 * `[1, , 2]` — and a `SpreadElement` is `...xs`. */
export interface ArrayExpression {
  type: "ArrayExpression";
  elements: (Expression | SpreadElement | null)[];
}

export interface ObjectExpression {
  type: "ObjectExpression";
  properties: (Property | SpreadElement | Unsupported)[];
}

export interface FunctionExpression {
  type: "FunctionExpression";
  id: Identifier | null;
  params: (Pattern | RestElement)[];
  body: BlockStatement;
  async: boolean;
  generator: boolean;
}

export interface ArrowFunctionExpression {
  type: "ArrowFunctionExpression";
  id: null;
  params: (Pattern | RestElement)[];
  body: BlockStatement | Expression;
  expression: boolean;
  async: boolean;
  generator: false;
}

export interface ConditionalExpression {
  type: "ConditionalExpression";
  test: Expression;
  consequent: Expression;
  alternate: Expression;
}

/** An assignment. `left` is an `ArrayPattern` or an `ObjectPattern` only
 * when `operator` is `"="`: a compound operator does not take a
 * pattern. */
export interface AssignmentExpression {
  type: "AssignmentExpression";
  operator: string;
  left: Expression | ArrayPattern | ObjectPattern;
  right: Expression;
}

export interface MethodDefinition {
  type: "MethodDefinition";
  key: Identifier | Literal | PrivateIdentifier;
  value: FunctionExpression;
  kind: "constructor" | "method" | "get" | "set";
  computed: false;
  static: boolean;
}

export interface PropertyDefinition {
  type: "PropertyDefinition";
  key: Identifier | Literal | PrivateIdentifier;
  value: Expression | null;
  computed: false;
  static: boolean;
}

export interface ClassBody {
  type: "ClassBody";
  body: (MethodDefinition | PropertyDefinition | Unsupported)[];
}

export interface ClassDeclaration {
  type: "ClassDeclaration";
  id: Identifier;
  superClass: Expression | null;
  body: ClassBody;
}

export interface ClassExpression {
  type: "ClassExpression";
  id: Identifier | null;
  superClass: Expression | null;
  body: ClassBody;
}

export type Expression =
  | Literal
  | Identifier
  | ThisExpression
  | UnaryExpression
  | UpdateExpression
  | BinaryExpression
  | LogicalExpression
  | ConditionalExpression
  | MemberExpression
  | CallExpression
  | NewExpression
  | ArrayExpression
  | ObjectExpression
  | FunctionExpression
  | ArrowFunctionExpression
  | AssignmentExpression
  | ClassExpression
  | TemplateLiteral
  | TaggedTemplateExpression
  | Unsupported;

export interface Directive {
  type: "ExpressionStatement";
  expression: Literal;
  directive: string;
}

export interface ExpressionStatement {
  type: "ExpressionStatement";
  expression: Expression;
}

export interface VariableDeclarator {
  type: "VariableDeclarator";
  id: Pattern;
  init: Expression | null;
}

export interface VariableDeclaration {
  type: "VariableDeclaration";
  kind: string;
  declarations: VariableDeclarator[];
}

export interface IfStatement {
  type: "IfStatement";
  test: Expression;
  consequent: Statement;
  alternate: Statement | null;
}

export interface WhileStatement {
  type: "WhileStatement";
  test: Expression;
  body: Statement;
}

/** `do { … } while (…)`. The body runs before the first test, which is
 * the whole of the difference from `while`; the body is named first here
 * as it is in the source. */
export interface DoWhileStatement {
  type: "DoWhileStatement";
  body: Statement;
  test: Expression;
}

export interface EmptyStatement {
  type: "EmptyStatement";
}

export interface ForStatement {
  type: "ForStatement";
  init: VariableDeclaration | Expression | null;
  test: Expression | null;
  update: Expression | null;
  body: Statement;
}

/** ESTree `ForInStatement`. The head is a declaration of exactly one
 * declarator with no initializer, an assignment target, or an assignment
 * pattern; the Lean decoder refuses every other shape by name. */
export interface ForInStatement {
  type: "ForInStatement";
  left: VariableDeclaration | Expression | ArrayPattern | ObjectPattern;
  right: Expression;
  body: Statement;
}

/** ESTree `ForOfStatement`. `await` is always false: `for await` is
 * async iteration, which is outside the epic, and the bridge refuses the
 * modifier in place. */
export interface ForOfStatement {
  type: "ForOfStatement";
  left: VariableDeclaration | Expression | ArrayPattern | ObjectPattern;
  right: Expression;
  body: Statement;
  await: false;
}

export interface SwitchCase {
  type: "SwitchCase";
  test: Expression | null;
  consequent: Statement[];
}

export interface SwitchStatement {
  type: "SwitchStatement";
  discriminant: Expression;
  cases: SwitchCase[];
}

export interface BlockStatement {
  type: "BlockStatement";
  body: Statement[];
}

export interface FunctionDeclaration {
  type: "FunctionDeclaration";
  id: Identifier;
  params: (Pattern | RestElement)[];
  body: BlockStatement;
  async: boolean;
  generator: boolean;
}

export interface ReturnStatement {
  type: "ReturnStatement";
  argument: Expression | null;
}

export interface ThrowStatement {
  type: "ThrowStatement";
  argument: Expression;
}

export interface CatchClause {
  type: "CatchClause";
  param: Pattern | null;
  body: BlockStatement;
}

export interface TryStatement {
  type: "TryStatement";
  block: BlockStatement;
  handler: CatchClause | null;
  finalizer: BlockStatement | null;
}

export interface LabeledStatement {
  type: "LabeledStatement";
  label: Identifier;
  body: Statement;
}

export interface BreakStatement {
  type: "BreakStatement";
  label: Identifier | null;
}

export interface ContinueStatement {
  type: "ContinueStatement";
  label: Identifier | null;
}

export type Statement =
  | Directive
  | ExpressionStatement
  | VariableDeclaration
  | FunctionDeclaration
  | ReturnStatement
  | IfStatement
  | WhileStatement
  | DoWhileStatement
  | ForStatement
  | ForInStatement
  | ForOfStatement
  | SwitchStatement
  | EmptyStatement
  | BlockStatement
  | ThrowStatement
  | TryStatement
  | LabeledStatement
  | BreakStatement
  | ContinueStatement
  | ClassDeclaration
  | Unsupported;

export interface Program {
  type: "Program";
  sourceType: "script";
  body: Statement[];
}

function unsupported(node: ts.Node): Unsupported {
  return { type: "Unsupported", kind: kindName(node.kind) };
}

/** The operator spelling ESTree uses, which is the source token. Every
 * operator token has one; only kinds that are not tokens do not. */
function operatorText(kind: ts.SyntaxKind): string {
  return ts.tokenToString(kind)!;
}

function rawText(node: ts.Node, sf: ts.SourceFile): string {
  return sf.text.slice(node.getStart(sf), node.end);
}

const ASSIGNMENT_OPERATORS = new Set([
  "=",
  "+=",
  "-=",
  "*=",
  "/=",
  "%=",
  "**=",
  "<<=",
  ">>=",
  ">>>=",
  "|=",
  "^=",
  "&=",
  "&&=",
  "||=",
  "??=",
]);

// ESTree calls these LogicalExpression, a node of its own, because they
// do not evaluate both operands. `??` is written out with them and
// refused on the Lean side.
const LOGICAL_OPERATORS = new Set(["&&", "||", "??"]);

/** `++` or `--`, for the two nodes that carry them; `undefined` for
 * every other prefix operator, which is an ordinary UnaryExpression. */
function updateOperator(kind: ts.SyntaxKind): "++" | "--" | undefined {
  if (kind === ts.SyntaxKind.PlusPlusToken) return "++";
  if (kind === ts.SyntaxKind.MinusMinusToken) return "--";
  return undefined;
}

/** A call's arguments, a spread in place. */
function callArguments(
  args: ts.NodeArray<ts.Expression>,
  sf: ts.SourceFile,
): (Expression | SpreadElement)[] {
  return args.map((a): Expression | SpreadElement =>
    ts.isSpreadElement(a)
      ? { type: "SpreadElement", argument: expression(a.expression, sf) }
      : expression(a, sf),
  );
}

/** A binding name: an `Identifier`, or one of the two binding patterns
 * through `bindingElement`. This is the *binding* half of the pattern
 * grammar; `assignmentTarget` is the other. */
function bindingName(name: ts.BindingName, sf: ts.SourceFile): Pattern {
  if (ts.isIdentifier(name)) return { type: "Identifier", name: name.text };
  if (ts.isArrayBindingPattern(name)) {
    const elements = name.elements.map((e): Pattern | RestElement | null =>
      ts.isOmittedExpression(e) ? null : bindingElement(e, sf),
    );
    return { type: "ArrayPattern", elements };
  }
  const properties = name.elements.map((e): PatternProperty | RestElement => {
    const bound = bindingElement(e, sf);
    if (bound.type === "RestElement") return bound;
    const key = e.propertyName ? propertyKey(e.propertyName, sf) : undefined;
    if (e.propertyName && !key) {
      // A `BigIntLiteral` or a private name as a property name: ESTree
      // has no node for either, so the property refuses in place.
      return {
        type: "Property",
        key: { type: "Identifier", name: "" },
        value: unsupported(e.propertyName),
        kind: "init",
        computed: false,
        shorthand: false,
        method: false,
      };
    }
    const shorthandKey: Expression = ts.isIdentifier(e.name)
      ? { type: "Identifier", name: e.name.text }
      : /* v8 ignore next -- a shorthand element's name is an identifier */
        unsupported(e.name);
    return {
      type: "Property",
      key: key ? key.key : shorthandKey,
      value: bound,
      kind: "init",
      computed: key ? key.computed : false,
      shorthand: !e.propertyName,
      method: false,
    };
  });
  return { type: "ObjectPattern", properties };
}

/** One element of a binding pattern: a rest marker makes a
 * `RestElement`, an initializer an `AssignmentPattern`, and the name
 * itself is a pattern. */
function bindingElement(
  e: ts.BindingElement,
  sf: ts.SourceFile,
): Pattern | RestElement {
  const inner = bindingName(e.name, sf);
  if (e.dotDotDotToken) return { type: "RestElement", argument: inner };
  if (e.initializer)
    return {
      type: "AssignmentPattern",
      left: inner,
      right: expression(e.initializer, sf),
    };
  return inner;
}

/** An assignment target: the *assignment* half of the pattern grammar.
 * tsc parses `[a, b] = xs` as an array literal on the left, so the
 * literal is re-read as a pattern here; anything that is not a literal
 * is an ordinary expression and the Lean decoder decides whether it is a
 * reference. */
function assignmentTarget(
  node: ts.Expression,
  sf: ts.SourceFile,
): Pattern | Expression {
  if (ts.isArrayLiteralExpression(node)) {
    const elements = node.elements.map((e): Pattern | RestElement | null => {
      if (ts.isOmittedExpression(e)) return null;
      if (ts.isSpreadElement(e))
        return {
          type: "RestElement",
          argument: patternTarget(e.expression, sf),
        };
      return patternTarget(e, sf);
    });
    return { type: "ArrayPattern", elements };
  }
  if (ts.isObjectLiteralExpression(node)) {
    const properties = node.properties.map(
      (m): PatternProperty | RestElement => {
        if (ts.isSpreadAssignment(m))
          return {
            type: "RestElement",
            argument: patternTarget(m.expression, sf),
          };
        if (ts.isShorthandPropertyAssignment(m)) {
          const name: Identifier = {
            type: "Identifier",
            name: m.name.text,
          };
          const value: Pattern = m.objectAssignmentInitializer
            ? {
                type: "AssignmentPattern",
                left: name,
                right: expression(m.objectAssignmentInitializer, sf),
              }
            : name;
          return {
            type: "Property",
            key: name,
            value,
            kind: "init",
            computed: false,
            shorthand: true,
            method: false,
          };
        }
        if (ts.isPropertyAssignment(m)) {
          const key = propertyKey(m.name, sf);
          return {
            type: "Property",
            key: key ? key.key : unsupported(m.name),
            value: patternTarget(m.initializer, sf),
            kind: "init",
            computed: key ? key.computed : false,
            shorthand: false,
            method: false,
          };
        }
        // A method or an accessor is not a target at all.
        return {
          type: "Property",
          key: { type: "Identifier", name: "" },
          value: unsupported(m),
          kind: "init",
          computed: false,
          shorthand: false,
          method: false,
        };
      },
    );
    return { type: "ObjectPattern", properties };
  }
  return expression(node, sf);
}

/** One element of an assignment pattern: a nested literal is a nested
 * pattern, a `=` is an `AssignmentPattern`, and everything else is a
 * reference the Lean decoder reads. */
function patternTarget(node: ts.Expression, sf: ts.SourceFile): Pattern {
  if (
    ts.isBinaryExpression(node) &&
    node.operatorToken.kind === ts.SyntaxKind.EqualsToken
  ) {
    return {
      type: "AssignmentPattern",
      left: patternTarget(node.left, sf),
      right: expression(node.right, sf),
    };
  }
  const inner = assignmentTarget(node, sf);
  if (
    inner.type === "ArrayPattern" ||
    inner.type === "ObjectPattern" ||
    inner.type === "Identifier" ||
    inner.type === "MemberExpression" ||
    inner.type === "Unsupported"
  )
    return inner;
  // Any other expression is not a target; the Lean decoder names it.
  return unsupported(node);
}

/** An object-literal member's key, and whether it was written in
 * brackets. A key ESTree has no node for — a `BigIntLiteral`, a private
 * name — is `undefined`, and the member is refused where it stands. */
function propertyKey(
  name: ts.PropertyName,
  sf: ts.SourceFile,
): { key: Expression; computed: boolean } | undefined {
  if (ts.isComputedPropertyName(name)) {
    return { key: expression(name.expression, sf), computed: true };
  }
  if (ts.isIdentifier(name)) {
    return { key: { type: "Identifier", name: name.text }, computed: false };
  }
  if (ts.isStringLiteral(name)) {
    return {
      key: { type: "Literal", value: name.text, raw: rawText(name, sf) },
      computed: false,
    };
  }
  if (ts.isNumericLiteral(name)) {
    return {
      key: {
        type: "Literal",
        value: Number(name.text),
        raw: rawText(name, sf),
      },
      computed: false,
    };
  }
  return undefined;
}

/** The `FunctionExpression` a method, getter, or setter's value is — in
 * a class body or in an object literal, which spell the same thing. A
 * TypeScript-only part of it refuses the member where it stands: a type
 * annotation, a `?` marker, a type parameter, or a missing body, which is
 * an ambient declaration a script cannot contain. */
function methodValue(
  m:
    | ts.MethodDeclaration
    | ts.GetAccessorDeclaration
    | ts.SetAccessorDeclaration,
  sf: ts.SourceFile,
): FunctionExpression | Unsupported {
  if (m.type) return unsupported(m.type);
  const questionToken = (m as ts.MethodDeclaration).questionToken;
  if (questionToken) return unsupported(questionToken);
  const typeParameter = (m as ts.MethodDeclaration).typeParameters?.[0];
  if (typeParameter) return unsupported(typeParameter);
  if (!m.body) return unsupported(m);
  const parts = functionParts(m as unknown as ts.FunctionExpression, sf);
  return {
    type: "FunctionExpression",
    id: null,
    params: parts.params,
    body: blockStatement(m.body, sf),
    async: parts.async,
    generator: parts.generator,
  };
}

/** Which of the three a method-like member defines. ESTree spells a
 * plain method as `kind: "init"` with `method: true`, and an accessor by
 * its `kind`. */
function accessorKind(m: ts.Node): "get" | "set" | "method" {
  if (ts.isGetAccessorDeclaration(m)) return "get";
  if (ts.isSetAccessorDeclaration(m)) return "set";
  return "method";
}

/** One member of an object literal. Every form is in the slice:
 * `key: value`, a shorthand, a computed key, a method, a getter, a
 * setter, and spread. */
function objectMember(
  member: ts.ObjectLiteralElementLike,
  sf: ts.SourceFile,
): Property | SpreadElement | Unsupported {
  if (ts.isSpreadAssignment(member)) {
    return {
      type: "SpreadElement",
      argument: expression(member.expression, sf),
    };
  }
  if (ts.isShorthandPropertyAssignment(member)) {
    // `{ a = 1 }` is a CoverInitializedName: the cover grammar for a
    // destructuring pattern, not a literal member, so the `=` is what
    // leaves the slice.
    if (member.objectAssignmentInitializer) {
      return unsupported(member.equalsToken!);
    }
    const name: Identifier = { type: "Identifier", name: member.name.text };
    return {
      type: "Property",
      key: name,
      value: name,
      kind: "init",
      computed: false,
      shorthand: true,
      method: false,
    };
  }
  if (ts.isPropertyAssignment(member)) {
    const key = propertyKey(member.name, sf);
    if (!key) return unsupported(member.name);
    return {
      type: "Property",
      key: key.key,
      value: expression(member.initializer, sf),
      kind: "init",
      computed: key.computed,
      shorthand: false,
      method: false,
    };
  }
  if (
    ts.isMethodDeclaration(member) ||
    ts.isGetAccessorDeclaration(member) ||
    ts.isSetAccessorDeclaration(member)
  ) {
    const offending = offendingModifier(member);
    if (offending) return unsupported(offending);
    const value = methodValue(member, sf);
    if (value.type === "Unsupported") return value;
    const key = propertyKey(member.name, sf);
    if (!key) return unsupported(member.name);
    const kind = accessorKind(member);
    return {
      type: "Property",
      key: key.key,
      value,
      kind: kind === "method" ? "init" : kind,
      computed: key.computed,
      shorthand: false,
      method: kind === "method",
    };
  }
  return unsupported(member);
}

/** A function's body. One without a body is an ambient declaration,
 * which a script cannot contain — `function f();` is a syntax error, and
 * the bridge refuses a program that does not parse before it gets
 * here. */
function functionBody(
  node: ts.FunctionDeclaration | ts.FunctionExpression,
  sf: ts.SourceFile,
): BlockStatement {
  /* v8 ignore next -- see above: the body is always present */
  return node.body
    ? blockStatement(node.body, sf)
    : { type: "BlockStatement", body: [] };
}

/** A function declaration's name. One without a name is
 * `export default function () {}`, a module form; a script cannot
 * produce it. */
function declarationName(node: ts.FunctionDeclaration): string {
  /* v8 ignore next -- see above: the name is always present */
  return node.name ? node.name.text : "";
}

/** The parts every function form shares. A parameter with a default
 * becomes an `AssignmentPattern`, a rest marker a `RestElement`, and a
 * binding pattern the pattern it is; a parameter property is refused as
 * its modifier, which is the more useful name, and only the parameter
 * leaves the slice, not the function. */
function functionParts(
  node: ts.FunctionDeclaration | ts.FunctionExpression | ts.ArrowFunction,
  sf: ts.SourceFile,
): {
  params: (Pattern | RestElement)[];
  async: boolean;
  generator: boolean;
} {
  const params = node.parameters.map((p): Pattern | RestElement => {
    // A parameter property — `constructor(public x) {}` — declares and
    // assigns a field, which is not something the parameter's name says,
    // so the modifier itself is what leaves the slice.
    const modifier = (ts.getModifiers(p) ?? [])[0];
    if (modifier) return unsupported(modifier);
    const inner = bindingName(p.name, sf);
    if (p.dotDotDotToken) return { type: "RestElement", argument: inner };
    if (p.initializer)
      return {
        type: "AssignmentPattern",
        left: inner,
        right: expression(p.initializer, sf),
      };
    return inner;
  });
  const isAsync = (node.modifiers ?? []).some(
    (m) => m.kind === ts.SyntaxKind.AsyncKeyword,
  );
  const asterisk = ts.isArrowFunction(node) ? undefined : node.asteriskToken;
  return { params, async: isAsync, generator: Boolean(asterisk) };
}

/** A class member's key. A computed key is refused as the member it
 * keys, because the key is the only part of it outside the slice and a
 * member with no name is not a member. */
function memberKey(
  name: ts.PropertyName,
  sf: ts.SourceFile,
): Identifier | Literal | PrivateIdentifier | undefined {
  if (ts.isIdentifier(name)) return { type: "Identifier", name: name.text };
  if (ts.isPrivateIdentifier(name)) {
    // tsc keeps the `#`; ESTree does not.
    return { type: "PrivateIdentifier", name: name.text.slice(1) };
  }
  if (ts.isStringLiteral(name)) {
    return { type: "Literal", value: name.text, raw: rawText(name, sf) };
  }
  if (ts.isNumericLiteral(name)) {
    return {
      type: "Literal",
      value: Number(name.text),
      raw: rawText(name, sf),
    };
  }
  return undefined;
}

/** The modifiers a class member may carry and still be JavaScript.
 * `static` and `async` are the two; every other one tsc accepts in a
 * `.js` file — `private`, `readonly`, `abstract`, `declare`, `accessor`
 * — is TypeScript, and refuses the member where it stands. */
function offendingModifier(node: ts.Node): ts.Node | undefined {
  const modifiers = ts.canHaveModifiers(node)
    ? (ts.getModifiers(node) ?? [])
    : [];
  const decorators = ts.canHaveDecorators(node)
    ? (ts.getDecorators(node) ?? [])
    : [];
  if (decorators.length > 0) return decorators[0];
  return modifiers.find(
    (m) =>
      m.kind !== ts.SyntaxKind.StaticKeyword &&
      m.kind !== ts.SyntaxKind.AsyncKeyword,
  );
}

function isStatic(node: ts.Node): boolean {
  return Boolean(
    ts.getCombinedModifierFlags(node as ts.Declaration) &
    ts.ModifierFlags.Static,
  );
}

/** One member of a class body. A static block, a bodiless method, and
 * every TypeScript-only form — a type annotation, a `?` or `!` marker, a
 * modifier other than `static` or `async`, a decorator — is refused in
 * place, so the class around it still reaches the Lean decoder and the
 * refusal names the tsc kind it stood for. */
function classMember(
  m: ts.ClassElement,
  sf: ts.SourceFile,
): MethodDefinition | PropertyDefinition | Unsupported {
  const offending = offendingModifier(m);
  if (offending) return unsupported(offending);
  if (ts.isConstructorDeclaration(m)) {
    if (!m.body) return unsupported(m);
    const parts = functionParts(m as unknown as ts.FunctionExpression, sf);
    return {
      type: "MethodDefinition",
      key: { type: "Identifier", name: "constructor" },
      value: {
        type: "FunctionExpression",
        id: null,
        params: parts.params,
        body: blockStatement(m.body, sf),
        async: parts.async,
        generator: parts.generator,
      },
      kind: "constructor",
      computed: false,
      static: false,
    };
  }
  if (
    ts.isMethodDeclaration(m) ||
    ts.isGetAccessorDeclaration(m) ||
    ts.isSetAccessorDeclaration(m)
  ) {
    const value = methodValue(m, sf);
    if (value.type === "Unsupported") return value;
    const key = memberKey(m.name, sf);
    if (!key) return unsupported(m.name);
    return {
      type: "MethodDefinition",
      key,
      value,
      kind: accessorKind(m),
      computed: false,
      static: isStatic(m),
    };
  }
  if (ts.isPropertyDeclaration(m)) {
    if (m.type) return unsupported(m.type);
    if (m.questionToken) return unsupported(m.questionToken);
    if (m.exclamationToken) return unsupported(m.exclamationToken);
    const key = memberKey(m.name, sf);
    if (!key) return unsupported(m.name);
    return {
      type: "PropertyDefinition",
      key,
      value: m.initializer ? expression(m.initializer, sf) : null,
      computed: false,
      static: isStatic(m),
    };
  }
  return unsupported(m);
}

/** What a class declaration and a class expression share, before either
 * says which of the two it is. `type` is here only so that a refusal and
 * a class can be told apart. */
interface ClassParts {
  type: "ClassParts";
  id: Identifier | null;
  superClass: Expression | null;
  body: ClassBody;
}

/** A class declaration or expression. An `implements` clause, a type
 * parameter list, and a decorator are refusals of the whole class rather
 * than of one member: each says something about the class itself that
 * the slice cannot represent. A `;` between members carries no meaning
 * and is dropped. */
function classNode(
  node: ts.ClassDeclaration | ts.ClassExpression,
  sf: ts.SourceFile,
): ClassParts | Unsupported {
  const offending = offendingModifier(node);
  if (offending) return unsupported(offending);
  const typeParameter = node.typeParameters?.[0];
  if (typeParameter) return unsupported(typeParameter);
  let superClass: Expression | null = null;
  for (const clause of node.heritageClauses ?? []) {
    if (clause.token !== ts.SyntaxKind.ExtendsKeyword) {
      return unsupported(clause);
    }
    const base = clause.types[0];
    /* v8 ignore next -- an `extends` clause without a type does not parse */
    if (!base) return unsupported(clause);
    superClass = expression(base.expression, sf);
  }
  return {
    type: "ClassParts",
    id: node.name ? { type: "Identifier", name: node.name.text } : null,
    superClass,
    body: {
      type: "ClassBody",
      body: node.members
        .filter((m) => !ts.isSemicolonClassElement(m))
        .map((m) => classMember(m, sf)),
    },
  };
}

/** A member access's object, which may be `super`. */
function memberObject(
  node: ts.Expression,
  sf: ts.SourceFile,
): Expression | Super {
  return node.kind === ts.SyntaxKind.SuperKeyword
    ? { type: "Super" }
    : expression(node, sf);
}

/** `ts.TokenFlags.ContainsInvalidEscape`, which the public typings do not
 * export. tsc sets it on a template piece whose raw text holds an escape
 * the cooked grammar refuses, and then puts the raw text in `text` where
 * the cooked value would be — so the flag is the only way to tell the
 * two apart. Only a *tagged* template can carry one: elsewhere the escape
 * is a parse diagnostic, which `parseScript` reports as a `ParseError`. */
const CONTAINS_INVALID_ESCAPE = 2048;

/** One piece of a template's text. TRV normalizes `<CR><LF>` and a lone
 * `<CR>` to `<LF>`; tsc's `rawText` does not, so the bridge does. */
function templateElement(
  piece: ts.TemplateLiteralLikeNode,
  tail: boolean,
): TemplateElement {
  // tsc sets `templateFlags` on every piece it scans — `TokenFlags.None`
  // where there is nothing to say — but does not declare it in the public
  // typings.
  const flags = (piece as unknown as { templateFlags: number }).templateFlags;
  /* v8 ignore next -- every piece the parser produces has its raw text */
  const raw = piece.rawText ?? piece.text;
  return {
    type: "TemplateElement",
    value: {
      cooked: flags & CONTAINS_INVALID_ESCAPE ? null : piece.text,
      raw: raw.replace(/\r\n?/g, "\n"),
    },
    tail,
  };
}

/** A template's quasis and substitutions, tagged or not. tsc gives the
 * substitution-free form a literal node of its own and the other form a
 * head plus one span per substitution; ESTree spells both as two lists,
 * the quasis one longer. */
function templateLiteral(
  node: ts.TemplateLiteral,
  sf: ts.SourceFile,
): TemplateLiteral {
  if (ts.isNoSubstitutionTemplateLiteral(node)) {
    return {
      type: "TemplateLiteral",
      quasis: [templateElement(node, true)],
      expressions: [],
    };
  }
  const quasis: TemplateElement[] = [templateElement(node.head, false)];
  const expressions: Expression[] = [];
  for (const span of node.templateSpans) {
    expressions.push(expression(span.expression, sf));
    quasis.push(
      templateElement(
        span.literal,
        span.literal.kind === ts.SyntaxKind.TemplateTail,
      ),
    );
  }
  return { type: "TemplateLiteral", quasis, expressions };
}

function expression(node: ts.Expression, sf: ts.SourceFile): Expression {
  if (ts.isNumericLiteral(node)) {
    return {
      type: "Literal",
      value: Number(node.text),
      raw: rawText(node, sf),
    };
  }
  if (node.kind === ts.SyntaxKind.TrueKeyword) {
    return { type: "Literal", value: true, raw: "true" };
  }
  if (node.kind === ts.SyntaxKind.FalseKeyword) {
    return { type: "Literal", value: false, raw: "false" };
  }
  if (node.kind === ts.SyntaxKind.NullKeyword) {
    return { type: "Literal", value: null, raw: "null" };
  }
  if (ts.isStringLiteral(node)) {
    return { type: "Literal", value: node.text, raw: rawText(node, sf) };
  }
  // A template with no substitutions is a node kind of its own, and it is
  // still a `TemplateLiteral`: one quasi, no expressions.
  if (
    ts.isNoSubstitutionTemplateLiteral(node) ||
    ts.isTemplateExpression(node)
  ) {
    return templateLiteral(node, sf);
  }
  if (ts.isTaggedTemplateExpression(node)) {
    return {
      type: "TaggedTemplateExpression",
      tag: expression(node.tag, sf),
      quasi: templateLiteral(node.template, sf),
    };
  }
  if (ts.isIdentifier(node)) {
    return { type: "Identifier", name: node.text };
  }
  if (node.kind === ts.SyntaxKind.ThisKeyword) {
    return { type: "ThisExpression" };
  }
  // Parentheses carry no meaning past the parse: the tree already has the
  // grouping they expressed.
  if (ts.isParenthesizedExpression(node)) {
    return expression(node.expression, sf);
  }
  // tsc gives `typeof` and `void` each a node; ESTree spells both as
  // unary operators.
  if (ts.isTypeOfExpression(node)) {
    return {
      type: "UnaryExpression",
      operator: "typeof",
      argument: expression(node.expression, sf),
      prefix: true,
    };
  }
  if (ts.isVoidExpression(node)) {
    return {
      type: "UnaryExpression",
      operator: "void",
      argument: expression(node.expression, sf),
      prefix: true,
    };
  }
  if (ts.isDeleteExpression(node)) {
    return {
      type: "UnaryExpression",
      operator: "delete",
      argument: expression(node.expression, sf),
      prefix: true,
    };
  }
  if (ts.isPropertyAccessExpression(node)) {
    // An optional chain has semantics of its own — it short-circuits the
    // whole chain — so the access leaves the slice as a whole.
    if (node.questionDotToken) return unsupported(node);
    return {
      type: "MemberExpression",
      object: memberObject(node.expression, sf),
      property: ts.isIdentifier(node.name)
        ? { type: "Identifier", name: node.name.text }
        : /* v8 ignore next -- a dot access's name is one of the two */
          { type: "PrivateIdentifier", name: node.name.text.slice(1) },
      computed: false,
    };
  }
  if (ts.isElementAccessExpression(node)) {
    if (node.questionDotToken) return unsupported(node);
    return {
      type: "MemberExpression",
      object: memberObject(node.expression, sf),
      property: expression(node.argumentExpression, sf),
      computed: true,
    };
  }
  if (ts.isCallExpression(node)) {
    if (node.questionDotToken) return unsupported(node);
    return {
      type: "CallExpression",
      callee:
        node.expression.kind === ts.SyntaxKind.SuperKeyword
          ? { type: "Super" }
          : expression(node.expression, sf),
      arguments: callArguments(node.arguments, sf),
    };
  }
  if (ts.isClassExpression(node)) {
    const parts = classNode(node, sf);
    if (parts.type === "Unsupported") return parts;
    const { id, superClass, body } = parts;
    return { type: "ClassExpression", id, superClass, body };
  }
  if (ts.isNewExpression(node)) {
    return {
      type: "NewExpression",
      callee: expression(node.expression, sf),
      // `new F` with no argument list is an empty one in ESTree.
      arguments: callArguments(
        node.arguments ?? ts.factory.createNodeArray(),
        sf,
      ),
    };
  }
  if (ts.isArrayLiteralExpression(node)) {
    // An elision is a `null` element and a spread a `SpreadElement`,
    // which is ESTree's own shape for both.
    return {
      type: "ArrayExpression",
      elements: node.elements.map((e): Expression | SpreadElement | null =>
        ts.isOmittedExpression(e)
          ? null
          : ts.isSpreadElement(e)
            ? { type: "SpreadElement", argument: expression(e.expression, sf) }
            : expression(e, sf),
      ),
    };
  }
  if (ts.isObjectLiteralExpression(node)) {
    return {
      type: "ObjectExpression",
      properties: node.properties.map((m) => objectMember(m, sf)),
    };
  }
  if (ts.isFunctionExpression(node)) {
    const parts = functionParts(node, sf);
    return {
      type: "FunctionExpression",
      id: node.name ? { type: "Identifier", name: node.name.text } : null,
      params: parts.params,
      body: functionBody(node, sf),
      async: parts.async,
      generator: parts.generator,
    };
  }
  if (ts.isArrowFunction(node)) {
    const parts = functionParts(node, sf);
    const concise = !ts.isBlock(node.body);
    return {
      type: "ArrowFunctionExpression",
      id: null,
      params: parts.params,
      body: ts.isBlock(node.body)
        ? blockStatement(node.body, sf)
        : expression(node.body, sf),
      expression: concise,
      async: parts.async,
      generator: false,
    };
  }
  if (ts.isPrefixUnaryExpression(node)) {
    const update = updateOperator(node.operator);
    if (update) {
      return {
        type: "UpdateExpression",
        operator: update,
        argument: expression(node.operand, sf),
        prefix: true,
      };
    }
    return {
      type: "UnaryExpression",
      operator: operatorText(node.operator),
      argument: expression(node.operand, sf),
      prefix: true,
    };
  }
  if (ts.isPostfixUnaryExpression(node)) {
    // `++` and `--` are the only operators a postfix node can carry, so
    // the lookup never misses here; the prefix form shares it.
    return {
      type: "UpdateExpression",
      operator: node.operator === ts.SyntaxKind.PlusPlusToken ? "++" : "--",
      argument: expression(node.operand, sf),
      prefix: false,
    };
  }
  if (ts.isConditionalExpression(node)) {
    return {
      type: "ConditionalExpression",
      test: expression(node.condition, sf),
      consequent: expression(node.whenTrue, sf),
      alternate: expression(node.whenFalse, sf),
    };
  }
  if (ts.isBinaryExpression(node)) {
    const operator = operatorText(node.operatorToken.kind);
    // ESTree splits what tsc calls a BinaryExpression three ways.
    // Assignment and the short-circuiting operators are their own nodes;
    // only the last group is a BinaryExpression there too.
    if (ASSIGNMENT_OPERATORS.has(operator)) {
      // Only `=` takes a destructuring target; tsc parses that target as
      // a literal, so it is re-read as a pattern here.
      const left =
        operator === "="
          ? assignmentTarget(node.left, sf)
          : expression(node.left, sf);
      return {
        type: "AssignmentExpression",
        operator,
        left:
          left.type === "ArrayPattern" || left.type === "ObjectPattern"
            ? left
            : expression(node.left, sf),
        right: expression(node.right, sf),
      };
    }
    if (LOGICAL_OPERATORS.has(operator)) {
      return {
        type: "LogicalExpression",
        operator,
        left: expression(node.left, sf),
        right: expression(node.right, sf),
      };
    }
    return {
      type: "BinaryExpression",
      operator,
      left: expression(node.left, sf),
      right: expression(node.right, sf),
    };
  }
  return unsupported(node);
}

/** A declaration list's declarators. A declarator's `id` is a binding
 * name, so a destructuring declaration is a pattern here rather than a
 * refusal. */
function declarators(
  list: ts.VariableDeclarationList,
  sf: ts.SourceFile,
): VariableDeclarator[] {
  return list.declarations.map((d) => ({
    type: "VariableDeclarator" as const,
    id: bindingName(d.name, sf),
    init: d.initializer ? expression(d.initializer, sf) : null,
  }));
}

/** `let`, `const`, or `var` — the keyword the declaration list carries. */
function declarationKind(list: ts.VariableDeclarationList): string {
  if ((list.flags & ts.NodeFlags.Const) !== 0) return "const";
  if ((list.flags & ts.NodeFlags.Let) !== 0) return "let";
  return "var";
}

function blockStatement(node: ts.Block, sf: ts.SourceFile): BlockStatement {
  return {
    type: "BlockStatement",
    body: node.statements.map((s) => statement(s, sf)),
  };
}

/** A `catch` clause. The optional-binding form has no variable
 * declaration at all and gives `param: null`; every binding form,
 * patterns included, is a `Pattern`. */
function catchClause(node: ts.CatchClause, sf: ts.SourceFile): CatchClause {
  const declaration = node.variableDeclaration;
  return {
    type: "CatchClause",
    param: declaration ? bindingName(declaration.name, sf) : null,
    body: blockStatement(node.block, sf),
  };
}

/** A loop head's declaration-or-expression part, which `for`, `for`-`in`,
 * and `for`-`of` spell the same way. An array or object literal in an
 * assignment head is re-read as a pattern, which is what
 * `for ([a, b] of xs)` is. */
function forHead(
  node: ts.ForInitializer,
  sf: ts.SourceFile,
): VariableDeclaration | Expression | ArrayPattern | ObjectPattern {
  if (!ts.isVariableDeclarationList(node)) {
    const target = assignmentTarget(node, sf);
    if (target.type === "ArrayPattern" || target.type === "ObjectPattern")
      return target;
    return expression(node, sf);
  }
  return {
    type: "VariableDeclaration",
    kind: declarationKind(node),
    declarations: declarators(node, sf),
  };
}

/** A `for` head's first part, which unlike a `for`-`in`'s may be absent:
 * `for (;;)` has no initializer at all. */
function forInitializer(
  node: ts.ForInitializer | undefined,
  sf: ts.SourceFile,
): VariableDeclaration | Expression | null {
  if (!node) return null;
  if (!ts.isVariableDeclarationList(node)) return expression(node, sf);
  return {
    type: "VariableDeclaration",
    kind: declarationKind(node),
    declarations: declarators(node, sf),
  };
}

/** One `switch` clause. `default` is the one with no test; a clause is
 * not a block, so its statements are a bare list. */
function switchCase(
  node: ts.CaseOrDefaultClause,
  sf: ts.SourceFile,
): SwitchCase {
  return {
    type: "SwitchCase",
    test: ts.isCaseClause(node) ? expression(node.expression, sf) : null,
    consequent: node.statements.map((s) => statement(s, sf)),
  };
}

/** A `break` or `continue`'s target. */
function jumpLabel(node: ts.BreakOrContinueStatement): Identifier | null {
  return node.label ? { type: "Identifier", name: node.label.text } : null;
}

function statement(node: ts.Statement, sf: ts.SourceFile): Statement {
  if (ts.isExpressionStatement(node)) {
    return {
      type: "ExpressionStatement",
      expression: expression(node.expression, sf),
    };
  }
  if (ts.isVariableStatement(node)) {
    const list = node.declarationList;
    const declarations = declarators(list, sf);
    if (!declarations) return unsupported(node);
    return {
      type: "VariableDeclaration",
      kind: declarationKind(list),
      declarations,
    };
  }
  if (ts.isClassDeclaration(node)) {
    const parts = classNode(node, sf);
    if (parts.type === "Unsupported") return parts;
    const { id, superClass, body } = parts;
    // A class declaration always has a name in a script: the anonymous
    // form is `export default class {}`, a module form.
    /* v8 ignore next */
    if (!id) return unsupported(node);
    return { type: "ClassDeclaration", id, superClass, body };
  }
  if (ts.isFunctionDeclaration(node)) {
    const parts = functionParts(node, sf);
    return {
      type: "FunctionDeclaration",
      id: { type: "Identifier", name: declarationName(node) },
      params: parts.params,
      body: functionBody(node, sf),
      async: parts.async,
      generator: parts.generator,
    };
  }
  if (ts.isReturnStatement(node)) {
    return {
      type: "ReturnStatement",
      argument: node.expression ? expression(node.expression, sf) : null,
    };
  }
  if (ts.isIfStatement(node)) {
    return {
      type: "IfStatement",
      test: expression(node.expression, sf),
      consequent: statement(node.thenStatement, sf),
      alternate: node.elseStatement ? statement(node.elseStatement, sf) : null,
    };
  }
  if (ts.isWhileStatement(node)) {
    return {
      type: "WhileStatement",
      test: expression(node.expression, sf),
      body: statement(node.statement, sf),
    };
  }
  if (ts.isDoStatement(node)) {
    return {
      type: "DoWhileStatement",
      body: statement(node.statement, sf),
      test: expression(node.expression, sf),
    };
  }
  if (ts.isForStatement(node)) {
    return {
      type: "ForStatement",
      init: forInitializer(node.initializer, sf),
      test: node.condition ? expression(node.condition, sf) : null,
      update: node.incrementor ? expression(node.incrementor, sf) : null,
      body: statement(node.statement, sf),
    };
  }
  if (ts.isForInStatement(node)) {
    return {
      type: "ForInStatement",
      left: forHead(node.initializer, sf),
      right: expression(node.expression, sf),
      body: statement(node.statement, sf),
    };
  }
  if (ts.isForOfStatement(node)) {
    // `for await (… of …)` is async iteration, which is outside the
    // epic: the modifier is what leaves the slice, so the loop around it
    // does not need an arm of its own.
    if (node.awaitModifier) return unsupported(node.awaitModifier);
    return {
      type: "ForOfStatement",
      left: forHead(node.initializer, sf),
      right: expression(node.expression, sf),
      body: statement(node.statement, sf),
      await: false,
    };
  }
  if (ts.isSwitchStatement(node)) {
    return {
      type: "SwitchStatement",
      discriminant: expression(node.expression, sf),
      cases: node.caseBlock.clauses.map((c) => switchCase(c, sf)),
    };
  }
  if (ts.isEmptyStatement(node)) {
    return { type: "EmptyStatement" };
  }
  if (ts.isBlock(node)) {
    return blockStatement(node, sf);
  }
  if (ts.isThrowStatement(node)) {
    return {
      type: "ThrowStatement",
      argument: expression(node.expression, sf),
    };
  }
  if (ts.isTryStatement(node)) {
    return {
      type: "TryStatement",
      block: blockStatement(node.tryBlock, sf),
      handler: node.catchClause ? catchClause(node.catchClause, sf) : null,
      finalizer: node.finallyBlock
        ? blockStatement(node.finallyBlock, sf)
        : null,
    };
  }
  if (ts.isLabeledStatement(node)) {
    return {
      type: "LabeledStatement",
      label: { type: "Identifier", name: node.label.text },
      body: statement(node.statement, sf),
    };
  }
  if (ts.isBreakStatement(node)) {
    return { type: "BreakStatement", label: jumpLabel(node) };
  }
  if (ts.isContinueStatement(node)) {
    return { type: "ContinueStatement", label: jumpLabel(node) };
  }
  return unsupported(node);
}

/** Whether a statement is a directive-prologue entry: an expression
 * statement that is nothing but a string literal. */
function directiveOf(node: ts.Statement, sf: ts.SourceFile): Directive | null {
  if (!ts.isExpressionStatement(node)) return null;
  const e = node.expression;
  if (!ts.isStringLiteral(e)) return null;
  return {
    type: "ExpressionStatement",
    expression: { type: "Literal", value: e.text, raw: rawText(e, sf) },
    directive: e.text,
  };
}

/**
 * Parse one JavaScript source into the document the Lean evaluator reads.
 * `fileName` names the source in a syntax error and nowhere else: the
 * document carries no positions.
 */
export function parseScript(source: string, fileName: string): Program {
  const sf = ts.createSourceFile(
    fileName,
    source,
    ts.ScriptTarget.ES2023,
    true,
    ts.ScriptKind.JS,
  );
  const diags = (
    sf as unknown as { parseDiagnostics: readonly ts.Diagnostic[] }
  ).parseDiagnostics;
  const first = diags[0];
  if (first) {
    const message = ts.flattenDiagnosticMessageText(first.messageText, " ");
    /* v8 ignore next -- a parse diagnostic always has a position */
    const start = first.start ?? 0;
    const { line, character } = sf.getLineAndCharacterOfPosition(start);
    throw new ParseError(
      `${fileName}:${line + 1}:${character + 1}: ${message}`,
    );
  }

  const body: Statement[] = [];
  let inPrologue = true;
  for (const s of sf.statements) {
    const directive = inPrologue ? directiveOf(s, sf) : null;
    if (directive) {
      body.push(directive);
      continue;
    }
    inPrologue = false;
    body.push(statement(s, sf));
  }
  return { type: "Program", sourceType: "script", body };
}
