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
} from "./readings.js";
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
  | { kind: "unop"; op: "-" | "+" | "!"; operand: EmitExpr }
  | { kind: "binop"; op: string; left: EmitExpr; right: EmitExpr }
  | { kind: "same-value"; left: EmitExpr; right: EmitExpr }
  | { kind: "math-sqrt"; arg: EmitExpr }
  | { kind: "math-abs"; arg: EmitExpr }
  | { kind: "number-is-finite"; arg: EmitExpr }
  | { kind: "number-is-nan"; arg: EmitExpr }
  | { kind: "call"; callee: string; module?: string; args: EmitExpr[] }
  | { kind: "new"; className: string; module?: string; args: EmitExpr[] }
  | {
      kind: "getter-read";
      className: string;
      module?: string;
      name: string;
      object: EmitExpr;
    }
  | {
      kind: "field-read";
      className: string;
      module?: string;
      field: string;
      object: EmitExpr;
    }
  | { kind: "self" };

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
  | { kind: "if"; cond: EmitExpr; then: EmitStmt[]; else?: EmitStmt[] }
  | { kind: "field-set"; field: string; expr: EmitExpr };

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

export interface EmitGetter {
  name: string;
  body: EmitStmt[];
}

export interface EmitMethod {
  name: string;
  /** Parameter names; every parameter is `: number`. */
  params: string[];
  body: EmitStmt[];
}

/** A class as the emitter renders it: a structure over its fields, a
 * constructor that assigns each exactly once, and one function per
 * modeled getter or method. */
export interface EmitClass {
  kind: "class";
  name: string;
  /** The defining module's entry-relative path; absent for the entry. */
  module?: string;
  /** Field spellings in declaration order; a private one keeps its '#'. */
  fields: string[];
  source: string;
  ctor: { params: string[]; body: EmitStmt[] };
  getters: EmitGetter[];
  methods: EmitMethod[];
}

export type EmitDecl = EmitFunction | EmitClass;

/** What a use of a class needs to know: its fields in declaration order,
 * the getters that modeled, and its constructor's arity. */
export interface ClassShape {
  fields: string[];
  getters: ReadonlySet<string>;
  ctorArity: number;
  /** Modeled methods by name, with their arities. */
  methods: ReadonlyMap<string, number>;
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
  declarations: EmitDecl[];
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

/** The global number constants the walk models — exact binary64 values,
 * the fallback JavaScript makes them, never keywords. */
const GLOBAL_NUMBER_ATOMS = new Set(["NaN", "Infinity"]);

const ARITH_OPERATORS = new Set(["+", "-", "*", "/", "%"]);
const COMPARISON_OPERATORS = new Set(["<", "<=", ">", ">=", "===", "!=="]);
const LOGICAL_OPERATORS = new Set(["||", "&&"]);

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

/** A `this.F` read: the only receiver a member body can name. */
function isThisAccess(e: ts.Expression): e is ts.PropertyAccessExpression {
  return (
    ts.isPropertyAccessExpression(e) &&
    e.expression.kind === ts.SyntaxKind.ThisKeyword
  );
}

/** A `new C(...)` with a plain identifier callee — the only construction
 * shape the model reads. */
function newCall(e: ts.Expression): ts.NewExpression | undefined {
  const u = unwrapParens(e);
  if (!ts.isNewExpression(u)) return undefined;
  return ts.isIdentifier(u.expression) ? u : undefined;
}

/** A member access on a freshly built instance. */
function instanceAccess(
  e: ts.Expression,
): { object: ts.NewExpression; name: string } | undefined {
  if (!ts.isPropertyAccessExpression(e)) return undefined;
  const object = newCall(e.expression);
  if (object === undefined) return undefined;
  if (!ts.isIdentifier(e.name)) return undefined;
  return { object, name: e.name.text };
}

/** The class a `new` names, in the registries. */
function newRef(scope: WalkScope, built: ts.NewExpression): ModelRef {
  return refOf(scope, (built.expression as ts.Identifier).text);
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

function isPrefixNot(e: ts.Expression): e is ts.PrefixUnaryExpression {
  return (
    ts.isPrefixUnaryExpression(e) &&
    e.operator === ts.SyntaxKind.ExclamationToken
  );
}

/** Whether an expression's own shape can denote a number in this slice —
 * the shapes the typed walk accepts at `num`. Top-level shape only:
 * deeper offenders keep their own refusals. */
function numericShaped(e: ts.Expression, scope: WalkScope): boolean {
  const u = unwrapParens(e);
  if (ts.isNumericLiteral(u) || negatedLiteral(u) !== undefined) return true;
  if (ts.isIdentifier(u)) return true;
  if (isUnaryArith(u)) return true;
  if (ts.isBinaryExpression(u))
    return ARITH_OPERATORS.has(u.operatorToken.getText());
  if (isThisAccess(u) || instanceAccess(u) !== undefined) return true;
  const builtin = builtinCall(u, scope);
  if (builtin !== undefined) return builtin.ty === "num";
  return ts.isCallExpression(u) && ts.isIdentifier(u.expression);
}

/** Whether an expression's own shape can denote a boolean in this slice:
 * a comparison, a SameValue call, or a logical combination of them.
 * Top-level shape only: deeper offenders keep their own refusals. */
function booleanShaped(e: ts.Expression, scope: WalkScope): boolean {
  const u = unwrapParens(e);
  if (ts.isBinaryExpression(u)) {
    const op = u.operatorToken.getText();
    return COMPARISON_OPERATORS.has(op) || LOGICAL_OPERATORS.has(op);
  }
  if (isPrefixNot(u)) return true;
  if (builtinCall(u, scope)?.ty === "bool") return true;
  return equationSides(u) !== undefined;
}

/** Truthiness has no model: a logical operator is admitted only over
 * operands that are themselves modeled booleans. */
function nonBooleanOperand(
  op: string,
  which: string,
  operand: ts.Expression,
  sf: ts.SourceFile,
): FailedDecl {
  const inner = unwrapParens(operand);
  const { line, character } = sf.getLineAndCharacterOfPosition(
    inner.getStart(sf),
  );
  return {
    construct: op,
    reason:
      `'${op}' models boolean operands only; ${which} is not a boolean ` +
      `(${kindName(inner.kind)} at ${line + 1}:${character + 1})`,
  };
}

/** The first construct in tree order the old transcriber would have made
 * opaque: anything outside identifiers, numeric literals, unary ±,
 * parentheses, binary operators (any operator — meaning is checked
 * later), and calls of a plain identifier. */
function findConstruct(
  e: ts.Expression,
  sf: ts.SourceFile,
  scope: WalkScope,
): FailedDecl | undefined {
  if (ts.isParenthesizedExpression(e))
    return findConstruct(e.expression, sf, scope);
  if (ts.isIdentifier(e) || ts.isNumericLiteral(e)) return undefined;
  if (negatedLiteral(e) !== undefined) return undefined;
  if (isUnaryArith(e)) return findConstruct(e.operand, sf, scope);
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText();
    if (LOGICAL_OPERATORS.has(op)) {
      if (!booleanShaped(e.left, scope))
        return nonBooleanOperand(op, "the left operand", e.left, sf);
      if (!booleanShaped(e.right, scope))
        return nonBooleanOperand(op, "the right operand", e.right, sf);
    }
    return (
      findConstruct(e.left, sf, scope) ?? findConstruct(e.right, sf, scope)
    );
  }
  if (isPrefixNot(e)) {
    if (!booleanShaped(e.operand, scope))
      return nonBooleanOperand("!", "the operand", e.operand, sf);
    return findConstruct(e.operand, sf, scope);
  }
  const sides = equationSides(e);
  if (sides !== undefined) {
    // `Object.is` compares JS values of one type; only numbers have a
    // model here, so a non-numeric argument is refused on the merits.
    const offender = sides.findIndex((s) => !numericShaped(s, scope));
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
    return (
      findConstruct(sides[0]!, sf, scope) ?? findConstruct(sides[1]!, sf, scope)
    );
  }
  const builtin = builtinCall(e, scope);
  if (builtin !== undefined) return findConstruct(builtin.arg, sf, scope);
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    for (const a of e.arguments) {
      const found = findConstruct(a, sf, scope);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  // A field read is shaped only where `this` denotes something.
  if (isThisAccess(e) && scope.self !== undefined) return undefined;
  const access = instanceAccess(e);
  if (access !== undefined) return findConstruct(access.object, sf, scope);
  const built = newCall(e);
  if (built !== undefined) {
    const targ = built.typeArguments?.[0];
    if (targ !== undefined) return constructAt(targ, targ.kind, sf);
    for (const a of built.arguments ?? []) {
      const found = findConstruct(a, sf, scope);
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
  if (isPrefixNot(e)) return findRefusedOp(e.operand);
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText();
    const reason = REFUSED_OPERATORS.get(op);
    if (reason !== undefined) return { construct: op, reason };
    return findRefusedOp(e.left) ?? findRefusedOp(e.right);
  }
  const access = instanceAccess(e);
  if (access !== undefined) return findRefusedOp(access.object);
  const built = newCall(e);
  if (built !== undefined) {
    for (const a of built.arguments ?? []) {
      const found = findRefusedOp(a);
      if (found !== undefined) return found;
    }
    return undefined;
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
function callNames(
  e: ts.Expression,
  scope: WalkScope,
  into: string[] = [],
): string[] {
  if (ts.isParenthesizedExpression(e))
    return callNames(e.expression, scope, into);
  if (isUnaryArith(e)) return callNames(e.operand, scope, into);
  if (isPrefixNot(e)) return callNames(e.operand, scope, into);
  if (ts.isBinaryExpression(e)) {
    callNames(e.left, scope, into);
    return callNames(e.right, scope, into);
  }
  const sides = equationSides(e);
  if (sides !== undefined) {
    // `Object.is` has no callee of its own; its arguments carry them.
    callNames(sides[0], scope, into);
    return callNames(sides[1], scope, into);
  }
  const builtin = builtinCall(e, scope);
  // A builtin member call has no user callee; its argument carries them.
  if (builtin !== undefined) return callNames(builtin.arg, scope, into);
  const access = instanceAccess(e);
  if (access !== undefined) return callNames(access.object, scope, into);
  const built = newCall(e);
  if (built !== undefined) {
    // A class is not a callee, but its arguments carry them.
    for (const a of built.arguments ?? []) callNames(a, scope, into);
    return into;
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    into.push(e.expression.text);
    for (const a of e.arguments) callNames(a, scope, into);
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
  classes: ReadonlyMap<string, ClassShape>;
  /** Source spellings this module binds elsewhere: imported names, and
   * only those. A spelling absent here is this module's own. */
  names: ReadonlyMap<string, ModelRef>;
  /** This module's qualifier; empty for the entry file. */
  module: string;
  /** Set inside a getter body, where `this` denotes the instance. */
  self?: { ref: ModelRef; shape: ClassShape };
}

/** Whether the module itself binds a spelling: a top-level declaration or
 * a resolved import (`names`), or a degraded one (`failed`). */
function moduleBinds(scope: WalkScope, name: string): boolean {
  return (
    scope.names.has(name) ||
    scope.failed.has(modelKey({ module: scope.module, name }))
  );
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
  return failedCalleeIn(callNames(e, scope), scope);
}

/** A construct-carrying failure as it travels from a declaration to a
 * use; any other failure is left to the typed walk. */
function travelFailure(
  scope: WalkScope,
  ref: ModelRef,
): FailedDecl | undefined {
  const failed = scope.failed.get(modelKey(ref));
  if (failed?.construct === undefined) return undefined;
  return {
    construct: failed.construct,
    reason: `'${displayName(ref)}' could not be modeled: ${failed.reason}`,
  };
}

/** The first degraded class or class member a use names, in tree order:
 * `new C(...)` where C's declaration failed on a construct, or member
 * access on an instance whose member failed on one. */
function findFailedMemberUse(
  e: ts.Expression,
  scope: WalkScope,
): FailedDecl | undefined {
  if (ts.isParenthesizedExpression(e))
    return findFailedMemberUse(e.expression, scope);
  if (isUnaryArith(e) || isPrefixNot(e))
    return findFailedMemberUse(e.operand, scope);
  if (ts.isBinaryExpression(e)) {
    return (
      findFailedMemberUse(e.left, scope) ?? findFailedMemberUse(e.right, scope)
    );
  }
  const sides = equationSides(e);
  if (sides !== undefined) {
    return (
      findFailedMemberUse(sides[0], scope) ??
      findFailedMemberUse(sides[1], scope)
    );
  }
  const builtin = builtinCall(e, scope);
  if (builtin !== undefined) return findFailedMemberUse(builtin.arg, scope);
  const access = instanceAccess(e);
  if (access !== undefined) {
    const found = findFailedMemberUse(access.object, scope);
    if (found !== undefined) return found;
    const ref = newRef(scope, access.object);
    const shape = scope.classes.get(modelKey(ref));
    // An unmodeled class already travelled through its own `new`.
    if (shape === undefined) return undefined;
    if (shape.getters.has(access.name) || shape.fields.includes(access.name))
      return undefined;
    return travelFailure(scope, {
      module: ref.module,
      name: qualifiedName(access.name, ref.name),
    });
  }
  const built = newCall(e);
  if (built !== undefined) {
    const ref = newRef(scope, built);
    if (!scope.classes.has(modelKey(ref))) {
      const found = travelFailure(scope, ref);
      if (found !== undefined) return found;
    }
    for (const a of built.arguments ?? []) {
      const found = findFailedMemberUse(a, scope);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    for (const a of e.arguments) {
      const found = findFailedMemberUse(a, scope);
      if (found !== undefined) return found;
    }
  }
  return undefined;
}

type Expected = "num" | "bool";

function describeTy(t: Expected): string {
  return t === "num" ? "a number" : "a boolean";
}

/** An engine-route failure: the walk found something with no model, or a
 * type mismatch — the failures the old pipeline reports as `Error`. */
class ModelError extends Error {}

/** The shape of the class a `new` names, or the failure the use earns:
 * a bound name, a degraded declaration, a function, or nothing at all. */
function classShapeOf(scope: WalkScope, ref: ModelRef): ClassShape {
  const shape = scope.classes.get(modelKey(ref));
  if (shape !== undefined) return shape;
  const name = displayName(ref);
  if (scope.vars.has(ref.name) || scope.mapped.has(modelKey(ref))) {
    throw new ModelError(`'${name}' is not a class; 'new' has no model for it`);
  }
  const failed = scope.failed.get(modelKey(ref));
  if (failed !== undefined) {
    throw new ModelError(`'${name}' has no model: ${failed.reason}`);
  }
  throw new ModelError(`no model registered for '${name}'`);
}

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
    const bound = scope.vars.has(e.text);
    const global =
      !bound && GLOBAL_NUMBER_ATOMS.has(e.text) && !moduleBinds(scope, e.text);
    if (!bound && !global) {
      throw new ModelError(`unbound identifier '${e.text}'`);
    }
    if (expected !== "num") {
      throw new ModelError(
        `identifier '${e.text}' is a number, not ${describeTy(expected)}`,
      );
    }
    return bound ? { kind: "id", name: e.text } : { kind: "num", lit: e.text };
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
  if (isPrefixNot(e)) {
    const operand = walkTyped(e.operand, "bool", scope, sf);
    if (expected !== "bool") {
      throw new ModelError(
        `operator '!' yields a boolean, not ${describeTy(expected)}`,
      );
    }
    return { kind: "unop", op: "!", operand };
  }
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText(sf);
    if (LOGICAL_OPERATORS.has(op)) {
      const left = walkTyped(e.left, "bool", scope, sf);
      const right = walkTyped(e.right, "bool", scope, sf);
      if (expected !== "bool") {
        throw new ModelError(
          `operator '${op}' yields a boolean, not ${describeTy(expected)}`,
        );
      }
      return { kind: "binop", op, left, right };
    }
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
  const builtin = builtinCall(e, scope);
  if (builtin !== undefined) {
    // The argument is typed before the position is, mirroring the binops.
    const arg = walkTyped(builtin.arg, "num", scope, sf);
    if (expected !== builtin.ty) {
      throw new ModelError(
        `a call to '${builtin.name}' yields ${describeTy(builtin.ty)}, ` +
          `not ${describeTy(expected)}`,
      );
    }
    return { kind: builtin.kind, arg };
  }
  // Outside a member the construct scan already made `this` opaque, so
  // the receiver is here whenever the walk reaches a field read.
  if (scope.self !== undefined && isThisAccess(e)) {
    const field = e.name.text;
    if (!scope.self.shape.fields.includes(field)) {
      throw new ModelError(
        `'this.${field}' does not name a field of '${scope.self.ref.name}'`,
      );
    }
    /* v8 ignore start -- no boolean position admits a field read: every
       one of them is gated on `booleanShaped`, which a `this` access is
       not. The throw mirrors the call case's, kept for the same defense. */
    if (expected !== "num") {
      throw new ModelError(
        `field '${field}' is a number, not ${describeTy(expected)}`,
      );
    }
    /* v8 ignore stop */
    return {
      kind: "field-read",
      className: scope.self.ref.name,
      ...(scope.self.ref.module !== ""
        ? { module: scope.self.ref.module }
        : {}),
      field,
      object: { kind: "self" },
    };
  }
  const access = instanceAccess(e);
  if (access !== undefined) {
    const ref = newRef(scope, access.object);
    const shape = classShapeOf(scope, ref);
    const rawArgs = access.object.arguments ?? [];
    if (shape.ctorArity !== rawArgs.length) {
      throw new ModelError(
        `'${displayName(ref)}' expects ${shape.ctorArity} argument(s), ` +
          `got ${rawArgs.length}`,
      );
    }
    if (expected !== "num") {
      throw new ModelError(
        `a member read yields a number, not ${describeTy(expected)}`,
      );
    }
    const module = ref.module !== "" ? { module: ref.module } : {};
    const object: EmitExpr = {
      kind: "new",
      className: ref.name,
      ...module,
      args: rawArgs.map((a) => walkTyped(a, "num", scope, sf)),
    };
    if (shape.getters.has(access.name)) {
      return {
        kind: "getter-read",
        className: ref.name,
        ...module,
        name: access.name,
        object,
      };
    }
    if (shape.fields.includes(access.name)) {
      return {
        kind: "field-read",
        className: ref.name,
        ...module,
        field: access.name,
        object,
      };
    }
    throw new ModelError(
      `'${displayName(ref)}' has no member '${access.name}' in the model`,
    );
  }
  const built = newCall(e);
  if (built !== undefined) {
    const ref = newRef(scope, built);
    // The class must exist before the instance can be refused as a value.
    classShapeOf(scope, ref);
    throw new ModelError(
      `'new ${displayName(ref)}(...)' yields an instance of ` +
        `'${displayName(ref)}', not a number`,
    );
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    const ref = refOf(scope, e.expression.text);
    const key = modelKey(ref);
    // A dependency's model is named the way its definition is: the old
    // pipeline never sees the importing module's spelling.
    const name = displayName(ref);
    if (scope.classes.has(key)) {
      throw new ModelError(
        `'${name}' is a class; it is only modeled under 'new'`,
      );
    }
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
    (r: ScanRoot) => findConstruct(r.expr, r.sf, scope),
    (r: ScanRoot) => findRefusedOp(r.expr),
    (r: ScanRoot) => findFailedCallee(r.expr, scope),
    (r: ScanRoot) => findFailedMemberUse(r.expr, scope),
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
  | { t: "field-set"; field: string; expr: ts.Expression }
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

/** A `this.F = e` statement, F spelled with or without '#'. */
function thisFieldAssignment(
  e: ts.Expression,
): { field: string; expr: ts.Expression } | undefined {
  if (!ts.isBinaryExpression(e)) return undefined;
  if (e.operatorToken.kind !== ts.SyntaxKind.EqualsToken) return undefined;
  const target = unwrapParens(e.left);
  if (!isThisAccess(target)) return undefined;
  return { field: target.name.text, expr: e.right };
}

/** One statement's `TStmt`s, mirroring the old transcriber's fallthrough:
 * whatever it cannot say becomes the opaque node it would have emitted. */
function structureStmt(
  s: ts.Statement,
  sf: ts.SourceFile,
  locals: Locals,
  scope: WalkScope,
  /** Set only inside a constructor body, where `this.F = e` is a field
   * assignment rather than an opaque statement. */
  ctorFields?: ReadonlySet<string>,
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
    if (ctorFields !== undefined) {
      const set = thisFieldAssignment(s.expression);
      if (set !== undefined && ctorFields.has(set.field))
        return [{ t: "field-set", field: set.field, expr: set.expr }];
    }
    const stmt = assignStmt(s.expression, locals);
    if (stmt !== undefined) return [stmt];
  }
  if (ts.isIfStatement(s)) {
    const inner = unwrapParens(s.expression);
    // The condition must be boolean-shaped — a comparison, an `Object.is`
    // call, or a logical combination of them: truthiness has no model.
    const cond = booleanShaped(inner, scope)
      ? { expr: inner }
      : { opaque: constructAt(inner, inner.kind, sf) };
    // An arm's locals are a copy, so its bindings do not escape it. A
    // non-block arm is the one statement it is, which is how an `else if`
    // arrives: a nested if alone in the else arm.
    const arm = (stmt: ts.Statement): TStmt[] => {
      const body = ts.isBlock(stmt) ? stmt.statements : [stmt];
      const armLocals: Locals = new Map(locals);
      return body.flatMap((b) =>
        structureStmt(b, sf, armLocals, scope, ctorFields),
      );
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
      case "field-set":
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
  scope: WalkScope,
): FailedDecl | undefined {
  for (const s of stmts) {
    switch (s.t) {
      case "opaque":
        return s.failure;
      case "return": {
        const found = findConstruct(s.expr, sf, scope);
        if (found !== undefined) return found;
        break;
      }
      case "decl": {
        const found = findConstruct(s.init, sf, scope);
        if (found !== undefined) return found;
        break;
      }
      case "assign":
      case "field-set": {
        const found = findConstruct(s.expr, sf, scope);
        if (found !== undefined) return found;
        break;
      }
      case "if": {
        if ("opaque" in s.cond) return s.cond.opaque;
        const found =
          findConstruct(s.cond.expr, sf, scope) ??
          treeConstruct(s.then, sf, scope) ??
          (s.else !== undefined ? treeConstruct(s.else, sf, scope) : undefined);
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
    case "field-set": {
      const expr = walk(s.expr, "num", vars);
      const tail = lowerTree(rest, vars, k, scope, sf);
      return [{ kind: "field-set", field: s.field, expr }, ...tail];
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

/** The pre-scans over a whole statement tree, in the old elaborator's
 * order — opaque constructs, then refused operators, then
 * construct-failed callees — dead code included. */
function bodyPrescan(
  tree: readonly TStmt[],
  sf: ts.SourceFile,
  scope: WalkScope,
): FailedDecl | undefined {
  const construct = treeConstruct(tree, sf, scope);
  if (construct !== undefined) return construct;
  const exprs = treeExprs(tree);
  for (const e of exprs) {
    const refused = findRefusedOp(e);
    if (refused !== undefined) return refused;
  }
  const callee = failedCalleeIn(
    exprs.flatMap((e) => callNames(e, scope)),
    scope,
  );
  if (callee !== undefined) return callee;
  for (const e of exprs) {
    const found = findFailedMemberUse(e, scope);
    if (found !== undefined) return found;
  }
  return undefined;
}

/** The synthesized vocabulary a member name may not take: the
 * constructor model, and the names Lean's structure command generates. */
const RESERVED_MEMBERS = new Set([
  "construct",
  "mk",
  "rec",
  "recOn",
  "casesOn",
  "brecOn",
  "below",
  "noConfusion",
  "noConfusionType",
]);

class CtorPrecondition extends Error {}

const PRECONDITION =
  "the class model requires every field assigned exactly once on every path";

/** Fields assigned on the falling-through paths of `stmts`, or "leaves"
 * when every path throws. Exactly-once is the checked precondition. */
function assignedFields(
  stmts: readonly TStmt[],
  before: ReadonlySet<string>,
  className: string,
): Set<string> | "leaves" {
  let assigned = new Set(before);
  for (const s of stmts) {
    if (s.t === "field-set") {
      if (assigned.has(s.field)) {
        throw new CtorPrecondition(
          `the constructor of '${className}' assigns field '${s.field}' ` +
            `more than once on a path; ${PRECONDITION}`,
        );
      }
      assigned.add(s.field);
    } else if (s.t === "throw") {
      return "leaves";
    } else if (s.t === "if") {
      const thn = assignedFields(s.then, assigned, className);
      const els = assignedFields(s.else ?? [], assigned, className);
      if (thn === "leaves" && els === "leaves") return "leaves";
      if (thn === "leaves") assigned = els as Set<string>;
      else if (els === "leaves") assigned = thn;
      else {
        const diff = [...thn]
          .filter((f) => !els.has(f))
          .concat([...els].filter((f) => !thn.has(f)));
        if (diff.length > 0) {
          throw new CtorPrecondition(
            `the constructor of '${className}' assigns field '${diff[0]}' ` +
              `on only some paths; ${PRECONDITION}`,
          );
        }
        assigned = thn;
      }
    }
  }
  return assigned;
}

/** The first `return` in a constructor body: a constructor's result is
 * the instance it built, so an explicit one is outside the slice. */
function treeReturn(stmts: readonly TStmt[]): ts.Expression | undefined {
  for (const s of stmts) {
    if (s.t === "return") return s.expr;
    if (s.t === "if") {
      const found = treeReturn(s.then) ?? treeReturn(s.else ?? []);
      if (found !== undefined) return found;
    }
  }
  return undefined;
}

/** The first field a statement list assigns through `this`, arms
 * included — a write only a constructor may make. */
function firstThisAssignment(
  stmts: readonly ts.Statement[],
  fields: ReadonlySet<string>,
): string | undefined {
  const arm = (x: ts.Statement) => (ts.isBlock(x) ? x.statements : [x]);
  for (const s of stmts) {
    if (ts.isExpressionStatement(s)) {
      const set = thisFieldAssignment(s.expression);
      if (set !== undefined && fields.has(set.field)) return set.field;
    }
    if (ts.isIfStatement(s)) {
      const found =
        firstThisAssignment(arm(s.thenStatement), fields) ??
        (s.elseStatement !== undefined
          ? firstThisAssignment(arm(s.elseStatement), fields)
          : undefined);
      if (found !== undefined) return found;
    }
  }
  return undefined;
}

function memberNameFailure(
  className: string,
  member: string,
  what: string,
): FailedDecl {
  return {
    construct: "class-member-name",
    reason: `class '${className}' ${what} '${member}'`,
  };
}

/** A constructor parameter passes the function-parameter check; a
 * modifier on it is a parameter property, which declares a field the
 * body never assigns. */
function ctorParamFailure(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  const mods = ts.getModifiers(p) ?? [];
  if (mods.length > 0) return constructAt(mods[0]!, mods[0]!.kind, sf);
  if (!ts.isIdentifier(p.name)) return constructAt(p.name, p.name.kind, sf);
  if (p.dotDotDotToken !== undefined)
    return constructAt(p.dotDotDotToken, p.dotDotDotToken.kind, sf);
  if (p.questionToken !== undefined || p.initializer !== undefined)
    return constructAt(p, p.kind, sf);
  if (p.type === undefined) return constructAt(p, p.kind, sf);
  if (p.type.kind !== ts.SyntaxKind.NumberKeyword)
    return constructAt(p.type, p.type.kind, sf);
  return undefined;
}

/** The modifier kinds a field may carry. `static` is handled apart: a
 * static field degrades alone, not with its class. */
const FIELD_MODIFIERS = new Set([
  ts.SyntaxKind.PublicKeyword,
  ts.SyntaxKind.PrivateKeyword,
  ts.SyntaxKind.ProtectedKeyword,
  ts.SyntaxKind.ReadonlyKeyword,
]);

function hasModifier(m: ts.ClassElement, kind: ts.SyntaxKind): boolean {
  return (ts.getModifiers(m as ts.HasModifiers) ?? []).some(
    (x) => x.kind === kind,
  );
}

interface ClassWalk {
  emit: EmitClass;
  shape: ClassShape;
  /** Members that degrade alone, by their full model key. */
  memberFailed: Map<string, FailedDecl>;
}

/** A class declaration's IR, or the failure that degrades the whole
 * class. Members outside the slice degrade alone unless the constructor
 * or a field is what fails: those are the model's spine. */
function walkClass(
  cls: ts.ClassDeclaration,
  sf: ts.SourceFile,
  c: EmitClosure,
  names: ReadonlyMap<string, ModelRef>,
  qualifier: string,
): ClassWalk | FailedDecl {
  const className = cls.name!.text;
  const memberKey = (member: string, isStatic = false) =>
    modelKey({
      module: qualifier,
      name: qualifiedName(member, className, isStatic),
    });
  const decorators = ts.getDecorators(cls) ?? [];
  if (decorators[0] !== undefined)
    return constructAt(decorators[0], decorators[0].kind, sf);
  const heritage = cls.heritageClauses?.[0];
  if (heritage !== undefined) return constructAt(heritage, heritage.kind, sf);
  const typeParam = cls.typeParameters?.[0];
  if (typeParam !== undefined)
    return constructAt(typeParam, typeParam.kind, sf);
  for (const m of ts.getModifiers(cls) ?? []) {
    if (
      m.kind === ts.SyntaxKind.AbstractKeyword ||
      m.kind === ts.SyntaxKind.DeclareKeyword
    ) {
      return constructAt(m, m.kind, sf);
    }
  }

  const fields: string[] = [];
  const ctors: ts.ConstructorDeclaration[] = [];
  const getterDecls: ts.GetAccessorDeclaration[] = [];
  const methodDecls: ts.MethodDeclaration[] = [];
  const overloadOnly: string[] = [];
  const memberFailed = new Map<string, FailedDecl>();
  for (const m of cls.members) {
    if (ts.isSemicolonClassElement(m)) continue;
    const memberDecorators = ts.getDecorators(m as ts.HasDecorators) ?? [];
    if (memberDecorators[0] !== undefined)
      return constructAt(memberDecorators[0], memberDecorators[0].kind, sf);
    if (
      ts.isIndexSignatureDeclaration(m) ||
      ts.isClassStaticBlockDeclaration(m) ||
      ts.isSetAccessorDeclaration(m)
    ) {
      return constructAt(m.name ?? m, m.kind, sf);
    }
    if (m.name !== undefined && ts.isComputedPropertyName(m.name))
      return constructAt(m.name, m.name.kind, sf);
    const isStatic = hasModifier(m, ts.SyntaxKind.StaticKeyword);
    const spelling =
      m.name !== undefined &&
      (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name))
        ? m.name.text
        : undefined;
    if (ts.isConstructorDeclaration(m)) {
      // A bodiless overload signature declares nothing, like a function's.
      if (m.body !== undefined) ctors.push(m);
      continue;
    }
    if (spelling === undefined) return constructAt(m, m.kind, sf);
    // Every static member degrades alone, whatever kind it is.
    if (isStatic) {
      memberFailed.set(memberKey(spelling, true), constructAt(m, m.kind, sf));
      continue;
    }
    if (ts.isPropertyDeclaration(m)) {
      for (const mod of ts.getModifiers(m) ?? []) {
        if (!FIELD_MODIFIERS.has(mod.kind))
          return constructAt(mod, mod.kind, sf);
      }
      if (m.initializer !== undefined || m.questionToken !== undefined)
        return constructAt(m, m.kind, sf);
      if (m.type === undefined) return constructAt(m, m.kind, sf);
      if (m.type.kind !== ts.SyntaxKind.NumberKeyword)
        return constructAt(m.type, m.type.kind, sf);
      if (RESERVED_MEMBERS.has(spelling))
        return memberNameFailure(className, spelling, "reserves the name");
      if (fields.includes(spelling))
        return memberNameFailure(className, spelling, "declares two fields");
      fields.push(spelling);
      continue;
    }
    if (ts.isGetAccessorDeclaration(m)) {
      const failure = getterFailure(m, className, spelling, sf);
      if (failure !== undefined) memberFailed.set(memberKey(spelling), failure);
      else getterDecls.push(m);
      continue;
    }
    if (ts.isMethodDeclaration(m)) {
      // A bodiless overload signature declares nothing, like a function's.
      if (m.body !== undefined) methodDecls.push(m);
      else overloadOnly.push(spelling);
      continue;
    }
    // Anything else a class body can hold degrades alone.
    memberFailed.set(memberKey(spelling), constructAt(m, m.kind, sf));
  }
  const bodied = new Set(
    methodDecls.map((m) => (m.name as ts.PropertyName & { text: string }).text),
  );
  for (const spelling of overloadOnly) {
    if (!bodied.has(spelling))
      memberFailed.set(memberKey(spelling), {
        construct: "MethodDeclaration",
        reason: `'${qualifiedName(spelling, className)}' has no implementation to model`,
      });
  }
  for (const g of getterDecls) {
    const spelling = (g.name as ts.Identifier).text;
    if (fields.includes(spelling))
      return memberNameFailure(
        className,
        spelling,
        "declares both a field and a getter named",
      );
  }
  const getterNames = new Set(
    getterDecls.map((g) => (g.name as ts.Identifier).text),
  );
  const seenMethods = new Set<string>();
  for (const m of methodDecls) {
    const spelling = (m.name as ts.Identifier | ts.PrivateIdentifier).text;
    if (fields.includes(spelling))
      return memberNameFailure(
        className,
        spelling,
        "declares both a field and a method named",
      );
    if (getterNames.has(spelling))
      return memberNameFailure(
        className,
        spelling,
        "declares both a getter and a method named",
      );
    if (seenMethods.has(spelling))
      return memberNameFailure(
        className,
        spelling,
        "declares two methods named",
      );
    seenMethods.add(spelling);
  }
  if (ctors.length === 0) {
    return {
      construct: "ClassDeclaration",
      reason: `class '${className}' has no constructor implementation to model`,
    };
  }
  if (ctors[1] !== undefined) return constructAt(ctors[1], ctors[1].kind, sf);
  const ctor = ctors[0]!;
  for (const p of ctor.parameters) {
    const failure = ctorParamFailure(p, sf);
    if (failure !== undefined) return failure;
  }
  const ctorParams = ctor.parameters.map((p) => (p.name as ts.Identifier).text);
  const base = {
    mapped: c.mapped,
    failed: c.failed,
    classes: c.classes,
    names,
    module: qualifier,
  };
  const ctorScope: WalkScope = { ...base, vars: new Set(ctorParams) };
  const fieldSet = new Set(fields);
  const ctorLocals: Locals = new Map(
    ctorParams.map((p) => [p, "mutable" as const]),
  );
  const tree = ctor.body!.statements.flatMap((s) =>
    structureStmt(s, sf, ctorLocals, ctorScope, fieldSet),
  );
  const returned = treeReturn(tree);
  if (returned !== undefined) {
    const stmt = returned.parent;
    return constructAt(stmt, stmt.kind, sf);
  }
  // The precondition is a statement about the constructor, so it is
  // checked ahead of the expression-level scans.
  let ctorBody: EmitStmt[];
  try {
    const assigned = assignedFields(tree, new Set(), className);
    if (assigned !== "leaves") {
      const missing = fields.find((f) => !assigned.has(f));
      if (missing !== undefined) {
        return {
          construct: "constructor",
          reason:
            `the constructor of '${className}' never assigns field ` +
            `'${missing}'; ${PRECONDITION}`,
        };
      }
    }
    const failure = bodyPrescan(tree, sf, ctorScope);
    if (failure !== undefined) return failure;
    // Falling off the end is a constructor's normal exit: the renderer
    // appends the instance return.
    ctorBody = lowerTree(tree, ctorParams, () => {}, ctorScope, sf);
  } catch (err) {
    if (err instanceof CtorPrecondition)
      return { construct: "constructor", reason: err.message };
    /* v8 ignore next -- the walk throws nothing else */
    if (!(err instanceof ModelError)) throw err;
    return { reason: err.message };
  }

  const methodArities = new Map<string, number>();
  const shape: ClassShape = {
    fields,
    getters: getterNames,
    ctorArity: ctorParams.length,
    methods: methodArities,
  };
  const self = { ref: { module: qualifier, name: className }, shape };
  const getters: EmitGetter[] = [];
  for (const g of getterDecls) {
    const spelling = (g.name as ts.Identifier).text;
    const written = firstThisAssignment(g.body!.statements, fieldSet);
    if (written !== undefined) {
      const member = qualifiedName(spelling, className);
      memberFailed.set(memberKey(spelling), {
        construct: "this-assignment",
        reason:
          `'${member}' assigns field '${written}' outside the constructor; ` +
          `instances are immutable after construction`,
      });
      continue;
    }
    const scope: WalkScope = { ...base, vars: new Set(), self };
    const body = g.body!.statements.flatMap((st) =>
      structureStmt(st, sf, new Map(), scope),
    );
    const failure = bodyPrescan(body, sf, scope);
    if (failure !== undefined) {
      memberFailed.set(memberKey(spelling), failure);
      continue;
    }
    try {
      getters.push({
        name: spelling,
        body: lowerTree(
          body,
          [],
          () => {
            throw new ModelError("the body must return on every path");
          },
          scope,
          sf,
        ),
      });
    } catch (err) {
      /* v8 ignore next -- the walk throws nothing else */
      if (!(err instanceof ModelError)) throw err;
      memberFailed.set(memberKey(spelling), { reason: err.message });
    }
  }
  // Getters render ahead of methods, so a getter body sees an empty
  // method map: a getter calling a method degrades alone.
  const methods: EmitMethod[] = [];
  for (const m of methodDecls) {
    const spelling = (m.name as ts.Identifier | ts.PrivateIdentifier).text;
    const failure = methodFailure(m, className, spelling, sf);
    if (failure !== undefined) {
      memberFailed.set(memberKey(spelling), failure);
      continue;
    }
    const written = firstThisAssignment(m.body!.statements, fieldSet);
    if (written !== undefined) {
      const member = qualifiedName(spelling, className);
      memberFailed.set(memberKey(spelling), {
        construct: "this-assignment",
        reason:
          `'${member}' assigns field '${written}' outside the constructor; ` +
          `instances are immutable after construction`,
      });
      continue;
    }
    const params = m.parameters.map((p) => (p.name as ts.Identifier).text);
    const scope: WalkScope = { ...base, vars: new Set(params), self };
    const locals: Locals = new Map(params.map((p) => [p, "mutable" as const]));
    const body = m.body!.statements.flatMap((st) =>
      structureStmt(st, sf, locals, scope),
    );
    const prescan = bodyPrescan(body, sf, scope);
    if (prescan !== undefined) {
      memberFailed.set(memberKey(spelling), prescan);
      continue;
    }
    try {
      methods.push({
        name: spelling,
        params,
        body: lowerTree(
          body,
          params,
          () => {
            throw new ModelError("the body must return on every path");
          },
          scope,
          sf,
        ),
      });
      methodArities.set(spelling, params.length);
    } catch (err) {
      /* v8 ignore next -- the walk throws nothing else */
      if (!(err instanceof ModelError)) throw err;
      memberFailed.set(memberKey(spelling), { reason: err.message });
    }
  }
  return {
    emit: {
      kind: "class",
      name: className,
      ...(qualifier !== "" ? { module: qualifier } : {}),
      source: cls.getText(sf),
      fields,
      ctor: { params: ctorParams, body: ctorBody },
      getters,
      methods,
    },
    shape: {
      ...shape,
      getters: new Set(getters.map((g) => g.name)),
      methods: methodArities,
    },
    memberFailed,
  };
}

/** A method outside the slice degrades alone: privacy, asynchrony, a
 * signature the model cannot read, or a name the model reserves. */
function methodFailure(
  m: ts.MethodDeclaration,
  className: string,
  spelling: string,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  if (
    ts.isPrivateIdentifier(m.name) ||
    hasModifier(m, ts.SyntaxKind.PrivateKeyword)
  )
    return constructAt(m.name, m.kind, sf);
  if (m.asteriskToken !== undefined) return constructAt(m, m.kind, sf);
  if (hasModifier(m, ts.SyntaxKind.AsyncKeyword))
    return constructAt(m, m.kind, sf);
  const typeParam = m.typeParameters?.[0];
  if (typeParam !== undefined)
    return constructAt(typeParam, typeParam.kind, sf);
  if (m.questionToken !== undefined) return constructAt(m, m.kind, sf);
  if (RESERVED_MEMBERS.has(spelling))
    return memberNameFailure(className, spelling, "reserves the name");
  for (const p of m.parameters) {
    const failure = ctorParamFailure(p, sf);
    if (failure !== undefined) return failure;
  }
  if (m.type === undefined) return constructAt(m, m.kind, sf);
  if (m.type.kind !== ts.SyntaxKind.NumberKeyword)
    return constructAt(m.type, m.type.kind, sf);
  return undefined;
}

/** A getter outside the slice degrades alone: privacy, a signature the
 * model cannot read, or a name the model reserves. */
function getterFailure(
  g: ts.GetAccessorDeclaration,
  className: string,
  spelling: string,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  if (
    ts.isPrivateIdentifier(g.name) ||
    hasModifier(g, ts.SyntaxKind.PrivateKeyword)
  )
    return constructAt(g.name, g.kind, sf);
  if (RESERVED_MEMBERS.has(spelling))
    return memberNameFailure(className, spelling, "reserves the name");
  if (g.parameters.length > 0 || g.body === undefined)
    return constructAt(g, g.kind, sf);
  if (g.type === undefined) return constructAt(g, g.kind, sf);
  if (g.type.kind !== ts.SyntaxKind.NumberKeyword)
    return constructAt(g.type, g.type.kind, sf);
  return undefined;
}

/** A function declaration's IR, or its failure. The slice covers `const`
 * and `let` locals, reassignment, `if`/`else`, `throw`, and `return`;
 * anything beyond it must degrade, not approximate. */
function walkFunction(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
  c: EmitClosure,
  names: ReadonlyMap<string, ModelRef>,
  module: string,
): EmitFunction | FailedDecl {
  const sig = signatureFailure(fn, sf);
  if (sig !== undefined) return sig;
  const params = fn.parameters.map((p) => (p.name as ts.Identifier).text);
  const scope: WalkScope = {
    vars: new Set(params),
    mapped: c.mapped,
    failed: c.failed,
    classes: c.classes,
    names,
    module,
  };
  // Parameters are assignable, the way JavaScript has them.
  const locals: Locals = new Map(params.map((p) => [p, "mutable" as const]));
  const tree = fn.body!.statements.flatMap((s) =>
    structureStmt(s, sf, locals, scope),
  );
  const prescan = bodyPrescan(tree, sf, scope);
  if (prescan !== undefined) return prescan;
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

type BuiltinKind =
  "math-sqrt" | "math-abs" | "number-is-finite" | "number-is-nan";

/** The builtin member calls with models, keyed by source spelling. The
 * namespaces are immutable objects of the standard library, so each entry
 * is a fixed unary primitive — `Math.pow` and every other member stays an
 * unmapped construct. */
const BUILTIN_MEMBER_CALLS: ReadonlyMap<
  string,
  { kind: BuiltinKind; ty: Expected }
> = new Map([
  ["Math.sqrt", { kind: "math-sqrt", ty: "num" }],
  ["Math.abs", { kind: "math-abs", ty: "num" }],
  ["Number.isFinite", { kind: "number-is-finite", ty: "bool" }],
  ["Number.isNaN", { kind: "number-is-nan", ty: "bool" }],
]);

/** The whitelisted builtin member call an expression is, if any. A
 * binding of the namespace spelling — parameter, local, module-level
 * declaration, or import, degraded ones included — wins over the builtin,
 * the way one wins over the `NaN`/`Infinity` atoms: the model would
 * otherwise state a claim about the standard library the source does not
 * make. */
function builtinCall(
  e: ts.Expression,
  scope: WalkScope,
):
  | { name: string; kind: BuiltinKind; ty: Expected; arg: ts.Expression }
  | undefined {
  if (!ts.isCallExpression(e) || e.arguments.length !== 1) return undefined;
  const callee = e.expression;
  if (
    !ts.isPropertyAccessExpression(callee) ||
    !ts.isIdentifier(callee.expression)
  ) {
    return undefined;
  }
  const namespace = callee.expression.text;
  if (scope.vars.has(namespace) || moduleBinds(scope, namespace)) {
    return undefined;
  }
  const name = `${namespace}.${callee.name.text}`;
  const entry = BUILTIN_MEMBER_CALLS.get(name);
  if (entry === undefined) return undefined;
  return { name, ...entry, arg: e.arguments[0]! };
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
 * conclusion atom. Every other connective degrades to bare. A formula
 * the model refuses (an opaque construct, a refused operator, a
 * construct-failed callee) classifies `Inappropriate` with the old
 * pipeline's reason; one the typed walk fails classifies `Error` the way a
 * failed property elaboration does. */
function obligationPayload(
  formula: string,
  mapped: ReadonlyMap<string, number>,
  failed: ReadonlyMap<string, FailedDecl>,
  classes: ReadonlyMap<string, ClassShape>,
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
      classes,
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
  declarations: EmitDecl[];
  mapped: Map<string, number>;
  failed: Map<string, FailedDecl>;
  classes: Map<string, ClassShape>;
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
      const walked = walkFunction(stmt, sf, c, names, qualifier);
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
      const walked = walkClass(stmt, sf, c, names, qualifier);
      if ("emit" in walked) {
        c.declarations.push(walked.emit);
        c.classes.set(key(className), walked.shape);
        c.mapped.set(
          key(qualifiedName("constructor", className)),
          walked.shape.ctorArity,
        );
        for (const g of walked.shape.getters) {
          c.mapped.set(key(qualifiedName(g, className)), 0);
        }
        for (const [m, arity] of walked.shape.methods) {
          c.mapped.set(key(qualifiedName(m, className)), arity);
        }
        for (const [k, v] of walked.memberFailed) c.failed.set(k, v);
        continue;
      }
      // A class-level failure is every member's failure: the model has no
      // structure to hang a surviving member on.
      c.failed.set(key(className), walked);
      for (const member of stmt.members) {
        const name = member.name;
        if (name === undefined || !ts.isIdentifier(name)) continue;
        const isStatic = (
          ts.getModifiers(member as ts.HasModifiers) ?? []
        ).some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
        c.failed.set(
          key(qualifiedName(name.text, className, isStatic)),
          walked,
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
    classes: new Map(),
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
    const result = obligationPayload(
      a.formula,
      mapped,
      failed,
      closure.classes,
      names,
      module,
    );
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
