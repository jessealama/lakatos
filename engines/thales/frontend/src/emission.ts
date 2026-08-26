import * as path from "node:path";
import ts from "typescript";
import {
  type Binder,
  clampedEndpoints,
  EmptyAfterClampError,
  extractFromSource,
  intInterval,
  type InvalidAnnotation,
  isClassDomain,
  parseBody,
  parsePrefix,
  qualifiedName,
  type RawAnnotation,
  unsupportedRangeReason,
} from "../../../../lemma/src/index.js";
import {
  bindingIdentifiers,
  chainReading,
  type FloatBound,
  kindName,
  numberBounds,
  numberToken,
} from "./transcribe.js";
import {
  type ModelRef,
  type ModuleReader,
  diskReader,
  displayName,
  modelKey,
  moduleQualifier,
  resolveImport,
} from "./module-graph.js";

/** A JS expression in the shapes the plain-Lean emitter renders. The
 * frontend records operator text verbatim; what an operator means is the
 * emitter's decision, so the walk here admits exactly the operators the
 * emitter renders and classifies everything else the way the old
 * pipeline's elaborator does. */
export type EmitExpr =
  | { kind: "num"; lit: string }
  | { kind: "id"; name: string }
  | { kind: "unop"; op: "-" | "+"; operand: EmitExpr }
  | { kind: "binop"; op: string; left: EmitExpr; right: EmitExpr }
  | { kind: "same-value"; left: EmitExpr; right: EmitExpr }
  | { kind: "call"; callee: string; module?: string; args: EmitExpr[] };

/** A statement in the shapes the plain-Lean emitter renders as Lean
 * do-notation: `const` and mutable `let` locals, reassignment, `if`/`else`
 * (arms may return, throw, or fall through), `throw`, and `return`. A
 * `throw` carries the error's constructor name alone — the message is a
 * string the value model has nothing to say about. */
export type EmitStmt =
  | { kind: "return"; expr: EmitExpr }
  | { kind: "throw"; error: string }
  | { kind: "const"; name: string; init: EmitExpr }
  | { kind: "let"; name: string; init: EmitExpr }
  | { kind: "assign"; name: string; expr: EmitExpr }
  | { kind: "if"; cond: EmitExpr; then: EmitStmt[]; else?: EmitStmt[] };

export interface EmitFunction {
  kind: "function";
  name: string;
  /** The defining module's entry-relative path; absent for the entry. */
  module?: string;
  /** Parameter names; every parameter is `: number`. */
  params: string[];
  /** The declaration's original text, echoed as comments above the def. */
  source: string;
  body: EmitStmt[];
}

/** A binder's denoted domain: a finite half-open integer range, the whole
 * int line, the naturals, or a `number` binder — the whole double line,
 * narrowed by whichever bounds its interval carries. The same shapes the
 * old grammar's binder constructors carry. */
export type EmitBinder =
  | { name: string; kind: "range"; lo: string; hi: string }
  | { name: string; kind: "int" }
  | { name: string; kind: "nat" }
  | { name: string; kind: "number"; lower?: FloatBound; upper?: FloatBound };

export interface EmitObligation {
  /** Qualified function name — the annotation identity's `function`. */
  function: string;
  property: string;
  /** Whitespace-normalized formula, echoed as a comment above the command. */
  formula: string;
  payload:
    | {
        kind: "structured";
        /** Nested binders, outermost first. */
        binders: EmitBinder[];
        /** Guard antecedents, outermost first, inside every binder. Absent
         * rather than empty when the formula has none. */
        guards?: EmitExpr[];
        conclusion:
          | { kind: "eq"; left: EmitExpr; right: EmitExpr }
          | { kind: "istrue"; expr: EmitExpr };
      }
    | { kind: "bare" };
}

/** What thales-emit consumes: one module's mappable declarations and the
 * obligations over them, in source order. */
export interface Emission {
  file: string;
  declarations: EmitFunction[];
  obligations: EmitObligation[];
}

/** An annotation the frontend itself settles: outside the model
 * (`Inappropriate`) or failed by the engine's own gaps (`Error`), with a
 * reason byte-identical to the old pipeline's — which is what the parity
 * harness pins. */
export interface ClassifiedAnnotation {
  annotation: RawAnnotation;
  szs: "Inappropriate" | "Error" | "NotTried";
  /** NotTried only: the envelope kind the CLI reports alongside. */
  kind?: "unsupported-range";
  reason: string;
}

export interface PlainEmission {
  emission: Emission;
  annotations: RawAnnotation[];
  invalid: InvalidAnnotation[];
  classified: ClassifiedAnnotation[];
}

/** Mirror of the old pipeline's `FailedDecl`: why a declaration is not in
 * the model, with a construct name exactly when the failure is a statement
 * about the input rather than about the engine. */
interface FailedDecl {
  construct?: string;
  reason: string;
}

/** Operators deliberately left without a model, and why — the mirror of
 * `unmodeledOperator?` in Model.lean, byte for byte. */
const REFUSED_OPERATORS = new Map<string, string>([
  [
    "**",
    "'**' is implementation-approximated in JavaScript, so any model would " +
      "certify results a conforming engine may disagree with",
  ],
]);

const ARITH_OPERATORS = new Set(["+", "-", "*", "/", "%"]);
const COMPARISON_OPERATORS = new Set(["<", "<=", ">", ">=", "===", "!=="]);

function unmappedMsg(construct: string, pos: string): string {
  return `unmapped TypeScript construct '${construct}' at ${pos}`;
}

function constructAt(
  node: ts.Node,
  kind: ts.SyntaxKind,
  sf: ts.SourceFile,
): FailedDecl {
  const { line, character } = sf.getLineAndCharacterOfPosition(
    node.getStart(sf),
  );
  const construct = kindName(kind);
  return {
    construct,
    reason: unmappedMsg(construct, `${line + 1}:${character + 1}`),
  };
}

function unwrapParens(e: ts.Expression): ts.Expression {
  return ts.isParenthesizedExpression(e) ? unwrapParens(e.expression) : e;
}

/** A folded negative numeric literal, the one prefix-minus shape that is
 * a literal rather than an operator application. */
function negatedLiteral(e: ts.Expression): ts.NumericLiteral | undefined {
  if (
    ts.isPrefixUnaryExpression(e) &&
    e.operator === ts.SyntaxKind.MinusToken &&
    ts.isNumericLiteral(e.operand)
  ) {
    return e.operand;
  }
  return undefined;
}

function isUnaryArith(e: ts.Expression): e is ts.PrefixUnaryExpression {
  return (
    ts.isPrefixUnaryExpression(e) &&
    (e.operator === ts.SyntaxKind.MinusToken ||
      e.operator === ts.SyntaxKind.PlusToken)
  );
}

/** Whether an expression's own shape can denote a number in this slice —
 * the shapes the typed walk accepts at `num`. Top-level shape only:
 * deeper offenders keep their own refusals. */
function numericShaped(e: ts.Expression): boolean {
  const u = unwrapParens(e);
  if (ts.isNumericLiteral(u) || negatedLiteral(u) !== undefined) return true;
  if (ts.isIdentifier(u)) return true;
  if (isUnaryArith(u)) return true;
  if (ts.isBinaryExpression(u))
    return ARITH_OPERATORS.has(u.operatorToken.getText());
  return ts.isCallExpression(u) && ts.isIdentifier(u.expression);
}

/** The first construct in tree order the old transcriber would have made
 * opaque: anything outside identifiers, numeric literals, unary ±,
 * parentheses, binary operators (any operator — meaning is checked
 * later), and calls of a plain identifier. */
function findConstruct(
  e: ts.Expression,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  if (ts.isParenthesizedExpression(e)) return findConstruct(e.expression, sf);
  if (ts.isIdentifier(e) || ts.isNumericLiteral(e)) return undefined;
  if (negatedLiteral(e) !== undefined) return undefined;
  if (isUnaryArith(e)) return findConstruct(e.operand, sf);
  if (ts.isBinaryExpression(e)) {
    return findConstruct(e.left, sf) ?? findConstruct(e.right, sf);
  }
  const sides = equationSides(e);
  if (sides !== undefined) {
    // `Object.is` compares JS values of one type; only numbers have a
    // model here, so a non-numeric argument is refused on the merits.
    const offender = sides.findIndex((s) => !numericShaped(s));
    if (offender !== -1) {
      const arg = unwrapParens(sides[offender]!);
      const { line, character } = sf.getLineAndCharacterOfPosition(
        arg.getStart(sf),
      );
      return {
        construct: "Object.is",
        reason:
          `'Object.is' models numbers only; argument ${offender + 1} is ` +
          `not a number (${kindName(arg.kind)} at ${line + 1}:${character + 1})`,
      };
    }
    return findConstruct(sides[0]!, sf) ?? findConstruct(sides[1]!, sf);
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    for (const a of e.arguments) {
      const found = findConstruct(a, sf);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  return constructAt(e, e.kind, sf);
}

/** The first refused operator in tree order, as a failure that names it.
 * Runs after the construct scan, like the old elaborator's pre-scans. */
function findRefusedOp(e: ts.Expression): FailedDecl | undefined {
  if (ts.isParenthesizedExpression(e)) return findRefusedOp(e.expression);
  if (isUnaryArith(e) && negatedLiteral(e) === undefined) {
    return findRefusedOp(e.operand);
  }
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText();
    const reason = REFUSED_OPERATORS.get(op);
    if (reason !== undefined) return { construct: op, reason };
    return findRefusedOp(e.left) ?? findRefusedOp(e.right);
  }
  if (ts.isCallExpression(e)) {
    for (const a of e.arguments) {
      const found = findRefusedOp(a);
      if (found !== undefined) return found;
    }
  }
  return undefined;
}

/** Every identifier-callee name in tree order. */
function callNames(e: ts.Expression, into: string[] = []): string[] {
  if (ts.isParenthesizedExpression(e)) return callNames(e.expression, into);
  if (isUnaryArith(e)) return callNames(e.operand, into);
  if (ts.isBinaryExpression(e)) {
    callNames(e.left, into);
    return callNames(e.right, into);
  }
  if (ts.isCallExpression(e)) {
    if (ts.isIdentifier(e.expression)) {
      into.push(e.expression.text);
      for (const a of e.arguments) callNames(a, into);
    } else {
      const sides = equationSides(e);
      if (sides !== undefined) {
        callNames(sides[0], into);
        callNames(sides[1], into);
      }
    }
  }
  return into;
}

/** What a body or formula may reference: bound value names, the models
 * registered so far, and the declarations that failed. Registries are
 * keyed across the whole closure, so a reference resolves through
 * `names` — which module a source spelling belongs to — before lookup. */
interface WalkScope {
  vars: ReadonlySet<string>;
  mapped: ReadonlyMap<string, number>;
  failed: ReadonlyMap<string, FailedDecl>;
  /** Source spellings this module binds elsewhere: imported names, and
   * only those. A spelling absent here is this module's own. */
  names: ReadonlyMap<string, ModelRef>;
  /** This module's qualifier; empty for the entry file. */
  module: string;
}

/** Where a source spelling's model lives: an imported binding names its
 * exporting module, anything else is this module's own. */
function refOf(scope: WalkScope, name: string): ModelRef {
  return scope.names.get(name) ?? { module: scope.module, name };
}

/** The first callee among `names` whose own declaration failed on a named
 * construct: the refusal travels with the call. A callee that failed for
 * any other reason is left to the typed walk, as the old elaborator leaves
 * it to `evalExpr`. */
function failedCalleeIn(
  names: readonly string[],
  scope: WalkScope,
): FailedDecl | undefined {
  for (const name of names) {
    const ref = refOf(scope, name);
    const key = modelKey(ref);
    if (scope.mapped.has(key)) continue;
    const failed = scope.failed.get(key);
    if (failed?.construct !== undefined) {
      return {
        construct: failed.construct,
        reason: `'${displayName(ref)}' could not be modeled: ${failed.reason}`,
      };
    }
  }
  return undefined;
}

function findFailedCallee(
  e: ts.Expression,
  scope: WalkScope,
): FailedDecl | undefined {
  return failedCalleeIn(callNames(e), scope);
}

type Expected = "num" | "bool";

function describeTy(t: Expected): string {
  return t === "num" ? "a number" : "a boolean";
}

/** An engine-route failure: the walk found something with no model, or a
 * type mismatch — the failures the old pipeline reports as `Error`. */
class ModelError extends Error {}

/** The typed walk, mirroring `evalExpr`: operand types are checked in the
 * old elaboration order so the first failure — and its message — is the
 * same one the old pipeline reports. */
function walkTyped(
  e: ts.Expression,
  expected: Expected,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  if (ts.isParenthesizedExpression(e)) {
    return walkTyped(e.expression, expected, scope, sf);
  }
  const negated = negatedLiteral(e);
  if (ts.isNumericLiteral(e) || negated !== undefined) {
    if (expected !== "num") {
      throw new ModelError(
        `a numeric literal cannot be ${describeTy(expected)}`,
      );
    }
    const lit =
      negated !== undefined
        ? `-${numberToken(negated)}`
        : numberToken(e as ts.NumericLiteral);
    return { kind: "num", lit };
  }
  if (ts.isIdentifier(e)) {
    if (!scope.vars.has(e.text)) {
      throw new ModelError(`unbound identifier '${e.text}'`);
    }
    if (expected !== "num") {
      throw new ModelError(
        `identifier '${e.text}' is a number, not ${describeTy(expected)}`,
      );
    }
    return { kind: "id", name: e.text };
  }
  if (isUnaryArith(e)) {
    const operand = walkTyped(e.operand, "num", scope, sf);
    const op = e.operator === ts.SyntaxKind.MinusToken ? "-" : "+";
    if (expected !== "num") {
      throw new ModelError(
        `operator '${op}' yields a number, not ${describeTy(expected)}`,
      );
    }
    return { kind: "unop", op, operand };
  }
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText(sf);
    const left = walkTyped(e.left, "num", scope, sf);
    const right = walkTyped(e.right, "num", scope, sf);
    if (ARITH_OPERATORS.has(op)) {
      if (expected !== "num") {
        throw new ModelError(
          `operator '${op}' yields a number, not ${describeTy(expected)}`,
        );
      }
      return { kind: "binop", op, left, right };
    }
    if (COMPARISON_OPERATORS.has(op)) {
      if (expected !== "bool") {
        throw new ModelError(
          `operator '${op}' yields a boolean, not ${describeTy(expected)}`,
        );
      }
      return { kind: "binop", op, left, right };
    }
    // A refused operator the pre-scans missed still refuses; anything
    // else has no model, which is the engine's problem.
    const refused = REFUSED_OPERATORS.get(op);
    if (refused !== undefined) throw new ModelError(refused);
    throw new ModelError(`operator '${op}' has no model in this slice`);
  }
  const sides = equationSides(e);
  if (sides !== undefined) {
    // Operands are typed before the position is, mirroring the binops.
    const left = walkTyped(sides[0], "num", scope, sf);
    const right = walkTyped(sides[1], "num", scope, sf);
    if (expected !== "bool") {
      throw new ModelError(
        `a call to 'Object.is' yields a boolean, not ${describeTy(expected)}`,
      );
    }
    return { kind: "same-value", left, right };
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    const ref = refOf(scope, e.expression.text);
    const key = modelKey(ref);
    // A dependency's model is named the way its definition is: the old
    // pipeline never sees the importing module's spelling.
    const name = displayName(ref);
    const arity = scope.mapped.get(key);
    if (arity === undefined) {
      const failed = scope.failed.get(key);
      if (failed !== undefined) {
        throw new ModelError(`'${name}' has no model: ${failed.reason}`);
      }
      throw new ModelError(`no model registered for '${name}'`);
    }
    if (arity !== e.arguments.length) {
      throw new ModelError(
        `'${name}' expects ${arity} argument(s), got ${e.arguments.length}`,
      );
    }
    if (expected !== "num") {
      throw new ModelError(
        `a call to '${name}' yields a number, not ${describeTy(expected)}`,
      );
    }
    const args = e.arguments.map((a) => walkTyped(a, "num", scope, sf));
    return {
      kind: "call",
      callee: ref.name,
      ...(ref.module !== "" ? { module: ref.module } : {}),
      args,
    };
  }
  // Unreachable after the construct scan; degrade like an opaque node.
  throw new ModelError(constructAt(e, e.kind, sf).reason);
}

/** One scanned expression with the file it was parsed from: each formula
 * atom parses on its own, so positions are only meaningful against it. */
interface ScanRoot {
  expr: ts.Expression;
  sf: ts.SourceFile;
}

/** The old elaborator's pre-scans — opaque constructs, then refused
 * operators, then construct-failed callees — each across every root
 * before the next begins. */
function prescanFailure(
  roots: readonly ScanRoot[],
  scope: WalkScope,
): FailedDecl | undefined {
  const scans = [
    (r: ScanRoot) => findConstruct(r.expr, r.sf),
    (r: ScanRoot) => findRefusedOp(r.expr),
    (r: ScanRoot) => findFailedCallee(r.expr, scope),
  ];
  for (const scan of scans) {
    for (const r of roots) {
      const found = scan(r);
      if (found !== undefined) return found;
    }
  }
  return undefined;
}

/** The typed walk with the engine's failures caught as a `FailedDecl`. */
function typedOrFailure(
  e: ts.Expression,
  expected: Expected,
  scope: WalkScope,
  sf: ts.SourceFile,
): { expr: EmitExpr } | FailedDecl {
  try {
    return { expr: walkTyped(e, expected, scope, sf) };
  } catch (err) {
    if (err instanceof ModelError) return { reason: err.message };
    throw err;
  }
}

/** The signature check `transcribeFunction` applies, as a failure. */
function signatureFailure(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  for (const m of fn.modifiers ?? []) {
    if (
      m.kind !== ts.SyntaxKind.ExportKeyword &&
      m.kind !== ts.SyntaxKind.DefaultKeyword
    ) {
      return constructAt(m, m.kind, sf);
    }
  }
  if (fn.asteriskToken !== undefined)
    return constructAt(fn.asteriskToken, fn.asteriskToken.kind, sf);
  for (const p of fn.parameters) {
    if (!ts.isIdentifier(p.name)) return constructAt(p.name, p.name.kind, sf);
    if (p.dotDotDotToken !== undefined)
      return constructAt(p.dotDotDotToken, p.dotDotDotToken.kind, sf);
    if (p.questionToken !== undefined || p.initializer !== undefined)
      return constructAt(p, p.kind, sf);
    if (p.type === undefined) return constructAt(p, p.kind, sf);
    if (p.type.kind !== ts.SyntaxKind.NumberKeyword)
      return constructAt(p.type, p.type.kind, sf);
  }
  if (fn.type === undefined || fn.body === undefined)
    return constructAt(fn, fn.kind, sf);
  if (fn.type.kind !== ts.SyntaxKind.NumberKeyword)
    return constructAt(fn.type, fn.type.kind, sf);
  return undefined;
}

/** Names a body binds itself, and whether each may be assigned — the old
 * transcriber's `Locals`, with the same discipline: a branch's arm gets
 * its own copy, and a redeclaration of a name from an enclosing scope is
 * refused rather than shadowed. */
type Locals = Map<string, "const" | "mutable">;

/** The statement tree as the old transcriber would have rendered it: each
 * node is either a mapped statement (its expressions still tsc nodes) or
 * the opaque failure the transcriber would have emitted in its place. */
type TStmt =
  | { t: "return"; expr: ts.Expression }
  | { t: "throw"; error: string }
  | { t: "decl"; mutable: boolean; name: string; init: ts.Expression }
  | { t: "assign"; name: string; expr: ts.Expression }
  | {
      t: "if";
      cond: { expr: ts.Expression } | { opaque: FailedDecl };
      then: TStmt[];
      else?: TStmt[];
    }
  | { t: "opaque"; failure: FailedDecl };

/** The error kind a `throw` carries — the constructor's name, exactly as
 * the old transcriber reads it; the message is discarded. */
function errorKind(e: ts.Expression): string | undefined {
  const inner = unwrapParens(e);
  if (!ts.isNewExpression(inner)) return undefined;
  if (!ts.isIdentifier(inner.expression)) return undefined;
  return inner.expression.text;
}

/** A declaration's `TStmt`s, or undefined when any declarator falls
 * outside the slice — `var`, `using`, destructuring, an uninitialized
 * `let`, a non-number type annotation, or a redeclaration of a name
 * already bound here. Locals set for earlier declarators persist even
 * when a later one fails, exactly as the old transcriber leaves them. */
function declStmts(
  s: ts.VariableStatement,
  locals: Locals,
): TStmt[] | undefined {
  const flags = s.declarationList.flags;
  const isConst = (flags & ts.NodeFlags.Const) !== 0;
  const isLet = (flags & ts.NodeFlags.Let) !== 0;
  if (!isConst && !isLet) return undefined;
  if ((flags & ts.NodeFlags.Using) !== 0) return undefined;
  if (s.declarationList.declarations.length === 0) return undefined;
  const stmts: TStmt[] = [];
  for (const d of s.declarationList.declarations) {
    if (!ts.isIdentifier(d.name)) return undefined;
    if (d.initializer === undefined) return undefined;
    if (d.type !== undefined && d.type.kind !== ts.SyntaxKind.NumberKeyword)
      return undefined;
    // Shadowing a name already bound here would make a join ambiguous: an
    // arm's own binding is what the tail would read back.
    if (locals.has(d.name.text)) return undefined;
    stmts.push({
      t: "decl",
      mutable: !isConst,
      name: d.name.text,
      init: d.initializer,
    });
    locals.set(d.name.text, isConst ? "const" : "mutable");
  }
  return stmts;
}

/** A reassignment of a mutable local, or undefined for anything else an
 * expression statement can be. */
function assignStmt(e: ts.Expression, locals: Locals): TStmt | undefined {
  if (!ts.isBinaryExpression(e)) return undefined;
  if (e.operatorToken.kind !== ts.SyntaxKind.EqualsToken) return undefined;
  const target = unwrapParens(e.left);
  if (!ts.isIdentifier(target)) return undefined;
  if (locals.get(target.text) !== "mutable") return undefined;
  return { t: "assign", name: target.text, expr: e.right };
}

/** One statement's `TStmt`s, mirroring the old transcriber's fallthrough:
 * whatever it cannot say becomes the opaque node it would have emitted. */
function structureStmt(
  s: ts.Statement,
  sf: ts.SourceFile,
  locals: Locals,
): TStmt[] {
  if (ts.isReturnStatement(s)) {
    // `return;` yields undefined, which a `number` function has no value
    // for and this slice does not model.
    if (s.expression === undefined)
      return [{ t: "opaque", failure: constructAt(s, s.kind, sf) }];
    return [{ t: "return", expr: s.expression }];
  }
  if (ts.isThrowStatement(s)) {
    const kind = errorKind(s.expression);
    if (kind !== undefined) return [{ t: "throw", error: kind }];
  }
  if (ts.isVariableStatement(s)) {
    const stmts = declStmts(s, locals);
    if (stmts !== undefined) return stmts;
  }
  if (ts.isExpressionStatement(s)) {
    const stmt = assignStmt(s.expression, locals);
    if (stmt !== undefined) return [stmt];
  }
  if (ts.isIfStatement(s)) {
    const inner = unwrapParens(s.expression);
    // The condition must be a comparison or an `Object.is` call:
    // truthiness coercion and the logical operators have no model.
    const cond =
      (ts.isBinaryExpression(inner) &&
        COMPARISON_OPERATORS.has(inner.operatorToken.getText(sf))) ||
      equationSides(inner) !== undefined
        ? { expr: inner }
        : { opaque: constructAt(inner, inner.kind, sf) };
    // An arm's locals are a copy, so its bindings do not escape it. A
    // non-block arm is the one statement it is, which is how an `else if`
    // arrives: a nested if alone in the else arm.
    const arm = (stmt: ts.Statement): TStmt[] => {
      const body = ts.isBlock(stmt) ? stmt.statements : [stmt];
      const armLocals: Locals = new Map(locals);
      return body.flatMap((b) => structureStmt(b, sf, armLocals));
    };
    const thenArm = arm(s.thenStatement);
    if (s.elseStatement === undefined)
      return [{ t: "if", cond, then: thenArm }];
    return [{ t: "if", cond, then: thenArm, else: arm(s.elseStatement) }];
  }
  return [{ t: "opaque", failure: constructAt(s, s.kind, sf) }];
}

/** The mapped expressions of a statement tree in tree order — the order
 * the old pipeline's pre-scans see them in the constructor text. An
 * opaque statement contributes nothing: the transcriber replaced its whole
 * subtree. The scan goes into branches, dead code included. */
function treeExprs(
  stmts: readonly TStmt[],
  into: ts.Expression[] = [],
): ts.Expression[] {
  for (const s of stmts) {
    switch (s.t) {
      case "return":
        into.push(s.expr);
        break;
      case "decl":
        into.push(s.init);
        break;
      case "assign":
        into.push(s.expr);
        break;
      case "if":
        // An opaque condition never reaches this scan: the construct scan
        // runs first and returns it as the declaration's failure.
        if ("expr" in s.cond) into.push(s.cond.expr);
        treeExprs(s.then, into);
        if (s.else !== undefined) treeExprs(s.else, into);
        break;
      default:
        break;
    }
  }
  return into;
}

/** The first opaque node in the statement tree, in tree order: an opaque
 * statement, an opaque condition, or an unmapped construct inside a mapped
 * expression — whichever the old pipeline's scan reaches first. */
function treeConstruct(
  stmts: readonly TStmt[],
  sf: ts.SourceFile,
): FailedDecl | undefined {
  for (const s of stmts) {
    switch (s.t) {
      case "opaque":
        return s.failure;
      case "return": {
        const found = findConstruct(s.expr, sf);
        if (found !== undefined) return found;
        break;
      }
      case "decl": {
        const found = findConstruct(s.init, sf);
        if (found !== undefined) return found;
        break;
      }
      case "assign": {
        const found = findConstruct(s.expr, sf);
        if (found !== undefined) return found;
        break;
      }
      case "if": {
        if ("opaque" in s.cond) return s.cond.opaque;
        const found =
          findConstruct(s.cond.expr, sf) ??
          treeConstruct(s.then, sf) ??
          (s.else !== undefined ? treeConstruct(s.else, sf) : undefined);
        if (found !== undefined) return found;
        break;
      }
      case "throw":
        break;
    }
  }
  return undefined;
}

/** Whether every path through a statement leaves the function — the old
 * lowering's `stmtLeaves`/`stmtsLeave`, verbatim. */
function stmtLeaves(s: TStmt): boolean {
  switch (s.t) {
    case "return":
    case "throw":
      return true;
    case "if":
      return s.else !== undefined && stmtsLeave(s.then) && stmtsLeave(s.else);
    default:
      return false;
  }
}

function stmtsLeave(stmts: readonly TStmt[]): boolean {
  return stmts.some(stmtLeaves);
}

/** The rest of the body, validated where control falls off a statement
 * list — the mirror of the old lowering's `Cont`, kept only for its two
 * observable effects: the order errors are discovered in, and the tail
 * statements it yields exactly once. */
type Cont = () => void;

/** Lowers a statement tree into the emitted statement list, walking every
 * expression in exactly the order the old `lowerStmts` elaborates them, so
 * the first failure — and its message — is the one the old pipeline
 * reports. A return or throw ends its path (what follows never reaches
 * the artifact); a branch's tail is validated once, in the old lowering's
 * join order, and stays after the branch — do-notation needs no join. */
function lowerTree(
  stmts: readonly TStmt[],
  vars: readonly string[],
  k: Cont,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitStmt[] {
  const walk = (
    e: ts.Expression,
    expected: Expected,
    names: readonly string[],
  ) => walkTyped(e, expected, { ...scope, vars: new Set(names) }, sf);
  if (stmts.length === 0) {
    k();
    return [];
  }
  const [s, ...rest] = stmts as [TStmt, ...TStmt[]];
  switch (s.t) {
    // A return or a throw ends this path; whatever follows is unreachable.
    case "return":
      return [{ kind: "return", expr: walk(s.expr, "num", vars) }];
    case "throw":
      return [{ kind: "throw", error: s.error }];
    case "decl": {
      // A binding whose scope is the rest of the list; a bind rather than
      // a substitution, so an unused initializer still evaluates.
      const init = walk(s.init, "num", vars);
      const tail = lowerTree(rest, [...vars, s.name], k, scope, sf);
      return [
        { kind: s.mutable ? "let" : "const", name: s.name, init },
        ...tail,
      ];
    }
    case "assign": {
      const expr = walk(s.expr, "num", vars);
      const tail = lowerTree(rest, vars, k, scope, sf);
      return [{ kind: "assign", name: s.name, expr }, ...tail];
    }
    /* v8 ignore start -- an opaque statement or condition is unreachable
       here: the construct scan already degraded the declaration. The throw
       mirrors the old elaborator's, kept for the same defense. */
    case "opaque":
      throw new ModelError(s.failure.reason);
    case "if": {
      if ("opaque" in s.cond) throw new ModelError(s.cond.opaque.reason);
      /* v8 ignore stop */
      const cond = walk(s.cond.expr, "bool", vars);
      const elseArm = s.else ?? [];
      // What an arm that falls through continues into: the rest of this
      // list, and only then the enclosing continuation.
      let tail: EmitStmt[] = [];
      let tailBuilt = false;
      const after: Cont = () => {
        /* v8 ignore next -- each continuation runs at most once by
           construction; the guard is the old lowering's invariant. */
        if (tailBuilt) return;
        tailBuilt = true;
        tail = lowerTree(rest, vars, k, scope, sf);
      };
      /* v8 ignore start -- the mirror of the old lowering's ruled-out
         continuation: an arm the leave-analysis proved leaving never
         invokes it, so it exists only to fail loudly on a bug. */
      const ruledOut: Cont = () => {
        throw new ModelError("the lowering reached an arm it had ruled out");
      };
      /* v8 ignore stop */
      const thenLeaves = stmtsLeave(s.then);
      const elseLeaves = stmtsLeave(elseArm);
      let thenK: Cont = ruledOut;
      let elseK: Cont = ruledOut;
      let deadTail = false;
      if (thenLeaves && elseLeaves) {
        // Both arms leave: the tail is unreachable, so it is never built.
        deadTail = true;
      } else if (thenLeaves) {
        elseK = after;
      } else if (elseLeaves) {
        thenK = after;
      } else {
        // Both arms fall through: the old lowering binds the tail as the
        // join before either arm, so it is validated first here too.
        after();
        thenK = () => {};
        elseK = () => {};
      }
      const thenIR = lowerTree(s.then, vars, thenK, scope, sf);
      const elseIR = lowerTree(elseArm, vars, elseK, scope, sf);
      const stmt: EmitStmt =
        s.else !== undefined && elseIR.length > 0
          ? { kind: "if", cond, then: thenIR, else: elseIR }
          : { kind: "if", cond, then: thenIR };
      return deadTail ? [stmt] : [stmt, ...tail];
    }
  }
}

/** A function declaration's IR, or its failure. The slice covers `const`
 * and `let` locals, reassignment, `if`/`else`, `throw`, and `return`;
 * anything beyond it must degrade, not approximate. */
function walkFunction(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
  mapped: ReadonlyMap<string, number>,
  failed: ReadonlyMap<string, FailedDecl>,
  names: ReadonlyMap<string, ModelRef>,
  module: string,
): EmitFunction | FailedDecl {
  const sig = signatureFailure(fn, sf);
  if (sig !== undefined) return sig;
  const params = fn.parameters.map((p) => (p.name as ts.Identifier).text);
  const scope: WalkScope = {
    vars: new Set(params),
    mapped,
    failed,
    names,
    module,
  };
  // Parameters are assignable, the way JavaScript has them.
  const locals: Locals = new Map(params.map((p) => [p, "mutable" as const]));
  const tree = fn.body!.statements.flatMap((s) => structureStmt(s, sf, locals));
  // The pre-scans cover the whole body in the old elaborator's order —
  // opaque constructs, then refused operators, then construct-failed
  // callees — dead code included.
  const construct = treeConstruct(tree, sf);
  if (construct !== undefined) return construct;
  const exprs = treeExprs(tree);
  for (const e of exprs) {
    const refused = findRefusedOp(e);
    if (refused !== undefined) return refused;
  }
  const callee = failedCalleeIn(
    exprs.flatMap((e) => callNames(e)),
    scope,
  );
  if (callee !== undefined) return callee;
  try {
    const body = lowerTree(
      tree,
      params,
      () => {
        // A `number` function that runs off the end returns undefined,
        // which this slice has no value for.
        throw new ModelError("the body must return on every path");
      },
      scope,
      sf,
    );
    return {
      kind: "function",
      name: fn.name!.text,
      ...(module !== "" ? { module } : {}),
      params,
      source: fn.getText(sf),
      body,
    };
  } catch (err) {
    if (err instanceof ModelError) return { reason: err.message };
    /* v8 ignore next 2 -- the walk throws nothing else */
    throw err;
  }
}

/** Parse one formula atom the way the transcriber does: wrapped in
 * parentheses, rejected on any parser diagnostic. */
function parseAtomExpr(
  js: string,
): { sf: ts.SourceFile; expr: ts.Expression } | undefined {
  const sf = ts.createSourceFile(
    "atom.ts",
    `(${js});`,
    ts.ScriptTarget.Latest,
    true,
  );
  const diags = (sf as unknown as { parseDiagnostics: readonly unknown[] })
    .parseDiagnostics;
  if (diags.length > 0) return undefined;
  const stmt = sf.statements[0] as ts.ExpressionStatement;
  return { sf, expr: stmt.expression };
}

/** The two sides of a desugared equation atom `Object.is(l, r)`. */
function equationSides(
  e: ts.Expression,
): [ts.Expression, ts.Expression] | undefined {
  if (!ts.isCallExpression(e) || e.arguments.length !== 2) return undefined;
  const callee = e.expression;
  if (
    !ts.isPropertyAccessExpression(callee) ||
    !ts.isIdentifier(callee.expression) ||
    callee.expression.text !== "Object" ||
    callee.name.text !== "is"
  ) {
    return undefined;
  }
  return [e.arguments[0]!, e.arguments[1]!];
}

/** A desugared `≢`: `!Object.is(…)`. The positive equation is a modeled
 * boolean atom now; the negation waits on `!` itself. */
function isNegatedEquation(e: ts.Expression): boolean {
  const inner = unwrapParens(e);
  return (
    ts.isPrefixUnaryExpression(inner) &&
    inner.operator === ts.SyntaxKind.ExclamationToken &&
    equationSides(unwrapParens(inner.operand)) !== undefined
  );
}

/** A binder's emitted domain: a finite half-open range, the whole int
 * line, the naturals, or a bounded `number` — reading the domain the binder
 * *denotes*, the same folding the old transcriber applies. `bare` covers
 * everything this slice cannot express; a safe-integer clamp reports its
 * offending endpoints instead, for the unsupported-range refusal. */
function lowerBinder(b: Binder): EmitBinder | "bare" | { clamped: string[] } {
  if (b.domain === "number") {
    // No safe-integer clamp: a number binder denotes binary64 values
    // directly, so there is no representability question to answer.
    const { lower, upper } = numberBounds(b.range);
    return {
      name: b.varName,
      kind: "number",
      ...(lower === undefined ? {} : { lower }),
      ...(upper === undefined ? {} : { upper }),
    };
  }
  if (b.domain !== "int" && b.domain !== "nat") return "bare";
  if (b.range === undefined) {
    return { name: b.varName, kind: b.domain === "nat" ? "nat" : "int" };
  }
  const { lo, hi } = intInterval(b.domain, b.range);
  if (hi === undefined) {
    if (lo === undefined) return { name: b.varName, kind: "int" };
    return lo === 0n ? { name: b.varName, kind: "nat" } : "bare";
  }
  if (lo === undefined) return "bare";
  const clamped = clampedEndpoints(b);
  if (clamped.length > 0) return { clamped };
  return {
    name: b.varName,
    kind: "range",
    lo: lo.toString(),
    hi: (hi + 1n).toString(),
  };
}

type PayloadResult =
  | { kind: "payload"; payload: EmitObligation["payload"] }
  | {
      kind: "classified";
      szs: "Inappropriate" | "Error" | "NotTried";
      classifiedKind?: "unsupported-range";
      reason: string;
    };

/** The structured reading of an annotation formula: int/nat binders and a
 * top-level implication chain of atoms — guard antecedents around one
 * conclusion atom. Every other connective degrades to bare, as does an
 * equation guard, which the boolean guard slot has no node for. A formula
 * the model refuses (an opaque construct, a refused operator, a
 * construct-failed callee) classifies `Inappropriate` with the old
 * pipeline's reason; one the typed walk fails classifies `Error` the way a
 * failed property elaboration does. */
function obligationPayload(
  formula: string,
  mapped: ReadonlyMap<string, number>,
  failed: ReadonlyMap<string, FailedDecl>,
  names: ReadonlyMap<string, ModelRef>,
  module: string,
): PayloadResult {
  const bare: PayloadResult = { kind: "payload", payload: { kind: "bare" } };
  try {
    const { binders, body } = parsePrefix(formula);
    const loweredBinders: EmitBinder[] = [];
    const clamped: string[] = [];
    for (const b of binders) {
      const lowered = lowerBinder(b);
      if (lowered === "bare") return bare;
      if ("clamped" in lowered) clamped.push(...lowered.clamped);
      else loweredBinders.push(lowered);
    }
    const chain = chainReading(parseBody(body));
    if (chain === undefined) return bare;
    const guardRoots: (ScanRoot & { expected: Expected })[] = [];
    for (const g of chain.guards) {
      const gp = parseAtomExpr(g);
      if (gp === undefined) return bare;
      if (isNegatedEquation(gp.expr)) return bare;
      guardRoots.push({
        expr: unwrapParens(gp.expr),
        sf: gp.sf,
        expected: "bool",
      });
    }
    const parsed = parseAtomExpr(chain.conclusion);
    if (parsed === undefined) return bare;
    // A clamp is reported only when it is the sole structuring blocker:
    // proving over the clamped domain would be a narrower statement.
    if (clamped.length > 0) {
      return {
        kind: "classified",
        szs: "NotTried",
        classifiedKind: "unsupported-range",
        reason: unsupportedRangeReason(clamped),
      };
    }
    const expr = unwrapParens(parsed.expr);
    const sides = equationSides(expr);
    const scope: WalkScope = {
      vars: new Set(binders.map((b) => b.varName)),
      mapped,
      failed,
      names,
      module,
    };
    // Guards precede the conclusion in the old elaborator's tree order, so
    // the first refusal either pipeline reports is the same one.
    const roots: (ScanRoot & { expected: Expected })[] = [
      ...guardRoots,
      ...(sides !== undefined
        ? [
            { expr: sides[0]!, sf: parsed.sf, expected: "num" as Expected },
            { expr: sides[1]!, sf: parsed.sf, expected: "num" as Expected },
          ]
        : [{ expr, sf: parsed.sf, expected: "bool" as Expected }]),
    ];
    // A property the model refuses is `Inappropriate`; one the typed walk
    // fails is a failed property elaboration, the engine's `Error`.
    const found = prescanFailure(roots, scope);
    if (found !== undefined) {
      return { kind: "classified", szs: "Inappropriate", reason: found.reason };
    }
    const walkedRoots: EmitExpr[] = [];
    for (const root of roots) {
      const walked = typedOrFailure(root.expr, root.expected, scope, root.sf);
      if (!("expr" in walked)) {
        return {
          kind: "classified",
          szs: "Error",
          reason: `property elaboration failed: ${walked.reason}`,
        };
      }
      walkedRoots.push(walked.expr);
    }
    const walkedGuards = walkedRoots.slice(0, guardRoots.length);
    const walkedConclusion = walkedRoots.slice(guardRoots.length);
    return {
      kind: "payload",
      payload: {
        kind: "structured",
        binders: loweredBinders,
        // Absent, not empty, when the formula has no guards.
        ...(walkedGuards.length > 0 ? { guards: walkedGuards } : {}),
        conclusion:
          sides !== undefined
            ? {
                kind: "eq",
                left: walkedConclusion[0]!,
                right: walkedConclusion[1]!,
              }
            : { kind: "istrue", expr: walkedConclusion[0]! },
      },
    };
  } catch (e) {
    // A clamp-emptied interval leaves no domain to prove over, whatever
    // the body: unsupported-range, like its merely-clamped kin.
    if (e instanceof EmptyAfterClampError) {
      return {
        kind: "classified",
        szs: "NotTried",
        classifiedKind: "unsupported-range",
        reason: unsupportedRangeReason(e.endpoints),
      };
    }
    return bare;
  }
}

/** The class-binder refusal, checked before everything else the way the
 * old transcriber checks it: outside the model whatever else the formula
 * or the function contains. */
function classBinderReason(formula: string): string | undefined {
  try {
    const { binders } = parsePrefix(formula);
    for (const b of binders) {
      if (isClassDomain(b.domain)) {
        return `class-valued binder '${b.domain.className}' is not yet modeled`;
      }
    }
  } catch {
    // The prefix parser's rejections degrade elsewhere.
  }
  return undefined;
}

/** One entry file's dependency-closure walk. Artifacts are
 * self-contained, so every module the entry reaches contributes its
 * declarations to the entry's own emission rather than being imported. */
interface EmitClosure {
  reader: ModuleReader;
  /** What module qualifiers are relative to: the entry file's directory. */
  entryDir: string;
  /** Modules already walked, by absolute path, with their name maps. */
  done: Map<string, ReadonlyMap<string, ModelRef>>;
  /** Modules whose walk has not finished: an import reaching back into
   * one closes a cycle. */
  active: Set<string>;
  declarations: EmitFunction[];
  mapped: Map<string, number>;
  failed: Map<string, FailedDecl>;
}

/** The top-level names a non-import declaration binds — what a reference
 * elsewhere in the module, or an importer, can name. Class members are
 * not among them: a member's key is synthesized, never written as an
 * identifier. */
function declaredNames(stmt: ts.Statement): string[] {
  if (ts.isVariableStatement(stmt)) {
    return stmt.declarationList.declarations.flatMap((d) =>
      bindingIdentifiers(d.name).map((id) => id.text),
    );
  }
  const name = (stmt as { name?: ts.Node }).name;
  return name !== undefined && ts.isIdentifier(name) ? [name.text] : [];
}

/** Walk `target` if it is not already in, and answer its name map. */
function inlineEmitModule(
  target: { file: string; text: string },
  c: EmitClosure,
): ReadonlyMap<string, ModelRef> {
  const done = c.done.get(target.file);
  if (done !== undefined) return done;
  c.active.add(target.file);
  const names = walkEmitModule(
    target.file,
    target.file,
    target.text,
    moduleQualifier(c.entryDir, target.file),
    c,
  );
  c.active.delete(target.file);
  c.done.set(target.file, names);
  return names;
}

/** Bind the names an import declaration introduces: to the exporting
 * module's models when the specifier resolves, opaquely otherwise — a
 * bare specifier, a relative one that reaches no file, a name that module
 * does not declare, or a specifier reaching a module still being walked,
 * which is an import cycle degrading at the edge that closes it. Default
 * and namespace imports name a module object, which the model has no
 * shape for, so they stay opaque however their specifier resolves. */
function bindEmitImport(
  stmt: ts.ImportDeclaration,
  from: string,
  names: Map<string, ModelRef>,
  qualifier: string,
  sf: ts.SourceFile,
  c: EmitClosure,
): void {
  const clause = stmt.importClause;
  if (clause === undefined) return;
  const degrade = (id: ts.Identifier) => {
    c.failed.set(
      modelKey({ module: qualifier, name: id.text }),
      constructAt(id, stmt.kind, sf),
    );
  };
  if (clause.name !== undefined) degrade(clause.name);
  const bindings = clause.namedBindings;
  if (bindings === undefined) return;
  if (ts.isNamespaceImport(bindings)) {
    degrade(bindings.name);
    return;
  }
  const specifier = stmt.moduleSpecifier;
  const target = ts.isStringLiteral(specifier)
    ? resolveImport(specifier.text, from, c.reader)
    : undefined;
  const exported =
    target === undefined || c.active.has(target.file)
      ? undefined
      : inlineEmitModule(target, c);
  for (const el of bindings.elements) {
    const to = exported?.get((el.propertyName ?? el.name).text);
    if (to === undefined) degrade(el.name);
    else names.set(el.name.text, to);
  }
}

/** Walk one module and, ahead of it, everything it imports. `label` is
 * what positions are reported against; `qualifier` is empty for the entry
 * file, whose names are the ones annotations are written about and so
 * keep their source spelling. */
function walkEmitModule(
  file: string,
  label: string,
  text: string,
  qualifier: string,
  c: EmitClosure,
): ReadonlyMap<string, ModelRef> {
  const sf = ts.createSourceFile(label, text, ts.ScriptTarget.Latest, true);
  const names = new Map<string, ModelRef>();
  const key = (name: string) => modelKey({ module: qualifier, name });
  // Bindings first, and dependencies with them: a call may precede the
  // declaration it names, and every dependency's declarations must be
  // registered before this module's bodies are walked.
  for (const stmt of sf.statements) {
    if (ts.isImportDeclaration(stmt)) {
      bindEmitImport(stmt, file, names, qualifier, sf, c);
    } else {
      for (const name of declaredNames(stmt)) {
        names.set(name, { module: qualifier, name });
      }
    }
  }
  for (const stmt of sf.statements) {
    if (ts.isFunctionDeclaration(stmt)) {
      if (stmt.name === undefined) continue;
      const walked = walkFunction(
        stmt,
        sf,
        c.mapped,
        c.failed,
        names,
        qualifier,
      );
      if ("kind" in walked && walked.kind === "function") {
        c.declarations.push(walked);
        c.mapped.set(key(stmt.name.text), walked.params.length);
      } else {
        c.failed.set(key(stmt.name.text), walked as FailedDecl);
      }
      continue;
    }
    if (ts.isClassDeclaration(stmt)) {
      if (stmt.name === undefined) continue;
      const className = stmt.name.text;
      c.failed.set(key(className), constructAt(stmt.name, stmt.kind, sf));
      for (const member of stmt.members) {
        const name = member.name;
        if (name === undefined || !ts.isIdentifier(name)) continue;
        const isStatic = (
          ts.getModifiers(member as ts.HasModifiers) ?? []
        ).some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
        c.failed.set(
          key(qualifiedName(name.text, className, isStatic)),
          constructAt(name, stmt.kind, sf),
        );
      }
      continue;
    }
    // Every other name a declaration binds degrades to the old pipeline's
    // opaque failure, position on the binding identifier.
    if (ts.isVariableStatement(stmt)) {
      for (const d of stmt.declarationList.declarations) {
        for (const id of bindingIdentifiers(d.name)) {
          c.failed.set(key(id.text), constructAt(id, stmt.kind, sf));
        }
      }
      continue;
    }
    // Import bindings were settled in the bindings pass above.
    if (ts.isImportDeclaration(stmt)) continue;
    // Any other named declaration (enum, interface, type alias, namespace).
    const name = (stmt as { name?: ts.Node }).name;
    if (name !== undefined && ts.isIdentifier(name)) {
      c.failed.set(key(name.text), constructAt(name, stmt.kind, sf));
    }
  }
  return names;
}

/**
 * Walk one module into the plain-Lean emission IR: mappable function
 * declarations with their bodies, one obligation per annotation on a
 * mapped function, and a frontend classification — with the old
 * pipeline's exact status and reason — for each annotation the model
 * refuses or the engine cannot attempt. The closure of the entry's
 * relative imports is walked ahead of it, each dependency's models
 * carrying their module; `file` locates the entry against the module tree
 * `reader` reads, and labels the annotations.
 */
export function emitModule(
  text: string,
  file: string,
  reader: ModuleReader = diskReader,
): PlainEmission {
  const entry = path.resolve(file);
  const closure: EmitClosure = {
    reader,
    entryDir: path.dirname(entry),
    done: new Map(),
    active: new Set([entry]),
    declarations: [],
    mapped: new Map(),
    failed: new Map(),
  };
  // The entry's qualifier is empty: its names are the ones annotations
  // are written about, so they keep their source spelling.
  const names = walkEmitModule(entry, file, text, "", closure);
  const { declarations, mapped, failed } = closure;
  const module = "";
  const key = (name: string) => modelKey({ module, name });

  const { annotations, invalid } = extractFromSource(text, file);
  const obligations: EmitObligation[] = [];
  const classified: ClassifiedAnnotation[] = [];
  for (const a of annotations) {
    const fn = qualifiedName(a.functionName, a.className, a.isStatic);
    const classBinder = classBinderReason(a.formula);
    if (classBinder !== undefined) {
      classified.push({
        annotation: a,
        szs: "Inappropriate",
        reason: classBinder,
      });
      continue;
    }
    // A failed declaration blocks the annotation only when nothing
    // modeled the name: an overload signature fails while the
    // implementation models.
    const fnFailed = mapped.has(key(fn)) ? undefined : failed.get(key(fn));
    if (fnFailed !== undefined) {
      classified.push({
        annotation: a,
        szs: fnFailed.construct !== undefined ? "Inappropriate" : "Error",
        reason: `'${fn}' could not be modeled: ${fnFailed.reason}`,
      });
      continue;
    }
    const result = obligationPayload(a.formula, mapped, failed, names, module);
    if (result.kind === "classified") {
      classified.push({
        annotation: a,
        szs: result.szs,
        ...(result.classifiedKind !== undefined
          ? { kind: result.classifiedKind }
          : {}),
        reason: result.reason,
      });
      continue;
    }
    obligations.push({
      function: fn,
      property: a.propertyName,
      formula: a.formula.replace(/\s+/g, " ").trim(),
      payload: result.payload,
    });
  }
  return {
    emission: { file, declarations, obligations },
    annotations,
    invalid,
    classified,
  };
}
