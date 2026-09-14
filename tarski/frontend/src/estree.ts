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

export interface MemberExpression {
  type: "MemberExpression";
  object: Expression;
  property: Expression;
  computed: boolean;
}

export interface CallExpression {
  type: "CallExpression";
  callee: Expression;
  arguments: Expression[];
}

export interface NewExpression {
  type: "NewExpression";
  callee: Expression;
  arguments: Expression[];
}

export interface Property {
  type: "Property";
  key: Literal | Identifier;
  value: Expression;
  kind: "init";
  computed: false;
  shorthand: false;
  method: false;
}

export interface ArrayExpression {
  type: "ArrayExpression";
  elements: Expression[];
}

export interface ObjectExpression {
  type: "ObjectExpression";
  properties: (Property | Unsupported)[];
}

export interface FunctionExpression {
  type: "FunctionExpression";
  id: Identifier | null;
  params: (Identifier | Unsupported)[];
  body: BlockStatement;
  async: boolean;
  generator: boolean;
}

export interface ArrowFunctionExpression {
  type: "ArrowFunctionExpression";
  id: null;
  params: (Identifier | Unsupported)[];
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

export interface AssignmentExpression {
  type: "AssignmentExpression";
  operator: string;
  left: Expression;
  right: Expression;
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
  id: Identifier;
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
  params: (Identifier | Unsupported)[];
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
  param: Identifier | Unsupported | null;
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
  | ForStatement
  | SwitchStatement
  | EmptyStatement
  | BlockStatement
  | ThrowStatement
  | TryStatement
  | LabeledStatement
  | BreakStatement
  | ContinueStatement
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

/** A call's arguments. A spread is outside the slice and stands in place
 * as `Unsupported`, so the call itself still reaches the Lean decoder. */
function callArguments(
  args: ts.NodeArray<ts.Expression>,
  sf: ts.SourceFile,
): Expression[] {
  return args.map((a) =>
    ts.isSpreadElement(a) ? unsupported(a) : expression(a, sf),
  );
}

/** One member of an object literal. Only `key: value` with an identifier,
 * string, or numeric key is in the slice; shorthand, methods, accessors,
 * computed keys, and spread stand in place as `Unsupported`. */
function objectMember(
  member: ts.ObjectLiteralElementLike,
  sf: ts.SourceFile,
): Property | Unsupported {
  if (!ts.isPropertyAssignment(member)) return unsupported(member);
  const name = member.name;
  let key: Literal | Identifier;
  if (ts.isIdentifier(name)) {
    key = { type: "Identifier", name: name.text };
  } else if (ts.isStringLiteral(name)) {
    key = { type: "Literal", value: name.text, raw: rawText(name, sf) };
  } else if (ts.isNumericLiteral(name)) {
    key = { type: "Literal", value: Number(name.text), raw: rawText(name, sf) };
  } else {
    return unsupported(name);
  }
  return {
    type: "Property",
    key,
    value: expression(member.initializer, sf),
    kind: "init",
    computed: false,
    shorthand: false,
    method: false,
  };
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

/** The parts every function form shares. A parameter with a default or a
 * rest marker is refused as the `Parameter` it is; a binding pattern is
 * refused as the pattern, which is the more useful name. Either way only
 * the parameter leaves the slice, not the function. */
function functionParts(
  node: ts.FunctionDeclaration | ts.FunctionExpression | ts.ArrowFunction,
): {
  params: (Identifier | Unsupported)[];
  async: boolean;
  generator: boolean;
} {
  const params = node.parameters.map((p): Identifier | Unsupported => {
    if (p.initializer || p.dotDotDotToken) return unsupported(p);
    if (!ts.isIdentifier(p.name)) return unsupported(p.name);
    return { type: "Identifier", name: p.name.text };
  });
  const isAsync = (node.modifiers ?? []).some(
    (m) => m.kind === ts.SyntaxKind.AsyncKeyword,
  );
  const asterisk = ts.isArrowFunction(node) ? undefined : node.asteriskToken;
  return { params, async: isAsync, generator: Boolean(asterisk) };
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
    // A template with no substitutions is a different node kind, and a
    // different literal: it stays outside the slice.
    return { type: "Literal", value: node.text, raw: rawText(node, sf) };
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
  if (ts.isPropertyAccessExpression(node)) {
    // An optional chain has semantics of its own — it short-circuits the
    // whole chain — so the access leaves the slice as a whole.
    if (node.questionDotToken) return unsupported(node);
    return {
      type: "MemberExpression",
      object: expression(node.expression, sf),
      property: ts.isIdentifier(node.name)
        ? { type: "Identifier", name: node.name.text }
        : unsupported(node.name),
      computed: false,
    };
  }
  if (ts.isElementAccessExpression(node)) {
    if (node.questionDotToken) return unsupported(node);
    return {
      type: "MemberExpression",
      object: expression(node.expression, sf),
      property: expression(node.argumentExpression, sf),
      computed: true,
    };
  }
  if (ts.isCallExpression(node)) {
    if (node.questionDotToken) return unsupported(node);
    return {
      type: "CallExpression",
      callee: expression(node.expression, sf),
      arguments: callArguments(node.arguments, sf),
    };
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
    // A hole and a spread are each refused where they stand, as a call's
    // spread argument is, so the literal around them still reaches the
    // Lean decoder.
    return {
      type: "ArrayExpression",
      elements: node.elements.map((e) =>
        ts.isOmittedExpression(e) || ts.isSpreadElement(e)
          ? unsupported(e)
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
    const parts = functionParts(node);
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
    const parts = functionParts(node);
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
      return {
        type: "AssignmentExpression",
        operator,
        left: expression(node.left, sf),
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

/** A declaration list's declarators, or `null` when one of them binds a
 * destructuring pattern: the schema's `id` is an Identifier, so such a
 * declaration leaves the slice as a whole rather than piecewise. */
function declarators(
  list: ts.VariableDeclarationList,
  sf: ts.SourceFile,
): VariableDeclarator[] | null {
  const out: VariableDeclarator[] = [];
  for (const d of list.declarations) {
    if (!ts.isIdentifier(d.name)) return null;
    out.push({
      type: "VariableDeclarator",
      id: { type: "Identifier", name: d.name.text },
      init: d.initializer ? expression(d.initializer, sf) : null,
    });
  }
  return out;
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
 * declaration at all and gives `param: null`; a destructuring binding is
 * outside the slice and is refused in place, as an out-of-slice parameter
 * is, so the clause and the `try` around it survive. */
function catchClause(node: ts.CatchClause, sf: ts.SourceFile): CatchClause {
  const declaration = node.variableDeclaration;
  let param: Identifier | Unsupported | null;
  if (!declaration) {
    param = null;
  } else if (ts.isIdentifier(declaration.name)) {
    param = { type: "Identifier", name: declaration.name.text };
  } else {
    param = unsupported(declaration.name);
  }
  return { type: "CatchClause", param, body: blockStatement(node.block, sf) };
}

/** A `for` head's first part: a declaration, an expression, or nothing.
 * A declaration binding a pattern is refused as a whole — the schema's
 * declarator `id` is an Identifier — and stands in the head's place, so
 * the loop around it still reaches the Lean decoder. */
function forInitializer(
  node: ts.ForInitializer | undefined,
  sf: ts.SourceFile,
): VariableDeclaration | Expression | null {
  if (!node) return null;
  if (!ts.isVariableDeclarationList(node)) return expression(node, sf);
  const declarations = declarators(node, sf);
  if (!declarations) return unsupported(node);
  return {
    type: "VariableDeclaration",
    kind: declarationKind(node),
    declarations,
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
  if (ts.isFunctionDeclaration(node)) {
    const parts = functionParts(node);
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
  if (ts.isForStatement(node)) {
    return {
      type: "ForStatement",
      init: forInitializer(node.initializer, sf),
      test: node.condition ? expression(node.condition, sf) : null,
      update: node.incrementor ? expression(node.incrementor, sf) : null,
      body: statement(node.statement, sf),
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
