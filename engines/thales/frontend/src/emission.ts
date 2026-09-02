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
  LemmaError,
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
  | { kind: "cond"; cond: EmitExpr; then: EmitExpr; else: EmitExpr }
  | { kind: "math-sqrt"; arg: EmitExpr }
  | { kind: "math-abs"; arg: EmitExpr }
  | { kind: "number-is-finite"; arg: EmitExpr }
  | { kind: "number-is-nan"; arg: EmitExpr }
  | { kind: "call"; callee: string; module?: string; args: EmitExpr[] }
  | { kind: "const-read"; name: string; module?: string }
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
  | {
      kind: "method-call";
      className: string;
      module?: string;
      name: string;
      object: EmitExpr;
      args: EmitExpr[];
    }
  | { kind: "self" }
  /** Injection into the tagged domain; `expr` is present exactly for the
   * payload-carrying `number` and `boolean` tags. */
  | { kind: "inject"; tag: UnionTag; expr?: EmitExpr }
  /** A union-typed read at a number position: the model refuses coercion,
   * so a wrong-tag value throws rather than converting. */
  | { kind: "project"; tag: "number"; expr: EmitExpr }
  /** A `typeof` test on a union-typed operand, against one of the eight
   * results `typeof` can answer. */
  | { kind: "typeof-test"; expr: EmitExpr; result: string }
  /** JS equality over the tagged domain: `===` as strict, `Object.is` as
   * same-value. Neither coerces, so a cross-tag pair is false. */
  | {
      kind: "jsval-eq";
      semantics: "strict" | "same-value";
      left: EmitExpr;
      right: EmitExpr;
    };

/** A statement in the shapes the plain-Lean emitter renders as Lean
 * do-notation: `const` and mutable `let` locals, reassignment, `if`/`else`
 * (arms may return, throw, or fall through), `throw`, and `return`. A
 * `throw` carries the error's constructor name alone — the message is a
 * string the value model has nothing to say about. */
export type EmitStmt =
  | { kind: "return"; expr: EmitExpr }
  | { kind: "throw"; error: string }
  /** A local's `type` is present exactly for a union binding — the same
   * normalized tag array a parameter's type carries; absent means the
   * numeric slice the statement always had. */
  | { kind: "const"; name: string; init: EmitExpr; type?: UnionTag[] }
  | { kind: "let"; name: string; init: EmitExpr; type?: UnionTag[] }
  | { kind: "assign"; name: string; expr: EmitExpr }
  | { kind: "if"; cond: EmitExpr; then: EmitStmt[]; else?: EmitStmt[] }
  | { kind: "field-set"; field: string; expr: EmitExpr };

/** A parameter on the wire: its name and its declared type — a TypeScript
 * number, a keyword union's normalized tags, or an instance of a modeled
 * class. */
export interface EmitParam {
  name: string;
  type: "number" | UnionTag[] | { class: string; module?: string };
}

export interface EmitFunction {
  kind: "function";
  name: string;
  /** The defining module's entry-relative path; absent for the entry. */
  module?: string;
  params: EmitParam[];
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
  params: EmitParam[];
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
  ctor: { params: EmitParam[]; body: EmitStmt[] };
  getters: EmitGetter[];
  methods: EmitMethod[];
}

/** A module-level `const` with a literal number initializer: a named
 * value the model admits, read wherever a number is expected. Soundness
 * needs two immutabilities at once: `const` pins the binding (a `let` or
 * `var` is reassignable from any function, so its reads have no one
 * value to model), and the numeric value pins itself — a primitive has
 * no mutable state, so no code can change what a read denotes. A
 * `const` over an object value would satisfy only the first, which is
 * why object initializers stay degraded. */
export interface EmitConstant {
  kind: "constant";
  name: string;
  /** The defining module's entry-relative path; absent for the entry. */
  module?: string;
  /** The literal's source text, unary minus included. */
  lit: string;
  source: string;
}

export type EmitDecl = EmitFunction | EmitClass | EmitConstant;

/** The union member tags the model admits, in normalization order. */
export const UNION_TAGS = [
  "number",
  "string",
  "bigint",
  "boolean",
  "undefined",
  "null",
] as const;
export type UnionTag = (typeof UNION_TAGS)[number];

/** A value's type in the walk: a number, a keyword union, or an instance
 * of a modeled class. Only parameters can carry the union and instance
 * types; locals, fields, and returns are numbers. */
export type ValueTy = "num" | { instance: ModelRef } | { union: UnionTag[] };

/** Whether two model references name the same class. */
function sameClass(a: ModelRef, b: ModelRef): boolean {
  return a.module === b.module && a.name === b.name;
}

/** A constructor parameter's type. Constructors keep the union ban, so a
 * class shape's parameters are numbers and instances only. */
export type CtorValueTy = "num" | { instance: ModelRef };

/** Whether two normalized unions are the same spelling — the only
 * relationship under which a union identifier flows to a union slot. */
function sameUnion(a: UnionTag[], b: UnionTag[]): boolean {
  return a.length === b.length && a.every((t, i) => t === b[i]);
}

function isUnionTy(t: Expected): t is { union: UnionTag[] } {
  return typeof t !== "string" && "union" in t;
}

/** The tag a union member denotes, when it is one of the keyword types;
 * `null` arrives as a literal-type node over the null token. */
function keywordTag(m: ts.TypeNode): UnionTag | undefined {
  switch (m.kind) {
    case ts.SyntaxKind.NumberKeyword:
      return "number";
    case ts.SyntaxKind.StringKeyword:
      return "string";
    case ts.SyntaxKind.BigIntKeyword:
      return "bigint";
    case ts.SyntaxKind.BooleanKeyword:
      return "boolean";
    case ts.SyntaxKind.UndefinedKeyword:
      return "undefined";
    default:
      return ts.isLiteralTypeNode(m) &&
        m.literal.kind === ts.SyntaxKind.NullKeyword
        ? "null"
        : undefined;
  }
}

/** A walked parameter as the wire carries it. */
function wireParam(name: string, ty: ValueTy): EmitParam {
  if (ty === "num") return { name, type: "number" };
  if ("union" in ty) return { name, type: [...ty.union] };
  const { module, name: cls } = ty.instance;
  return {
    name,
    type: { class: cls, ...(module !== "" ? { module } : {}) },
  };
}

/** A callable's signature: its parameter types in declaration order, and
 * how many of them a call must actually supply. Only trailing optionals
 * make the two differ — an optional's own type already carries the
 * `undefined` an omitted argument denotes, so arity is all that is left
 * to record, and it never reaches the wire. */
export interface FnSig {
  params: ValueTy[];
  required: number;
}

/** The signature a walked parameter list denotes. Optionals are trailing
 * by `walkParams`'s own check, so counting the required ones is enough. */
function sigOf(params: WalkedParams): FnSig {
  return {
    params: params.map((p) => p.ty),
    required: params.filter((p) => !p.optional).length,
  };
}

/** A fixed-arity signature: what a constructor or a getter has, neither
 * admitting an optional. */
function exactSig(params: ValueTy[]): FnSig {
  return { params, required: params.length };
}

/** The arity check every call shares. A call may omit trailing optionals
 * and nothing else; a signature without them keeps the single-count
 * message it has always reported. */
function checkArity(name: string, sig: FnSig, got: number): void {
  const total = sig.params.length;
  if (got >= sig.required && got <= total) return;
  const expected =
    sig.required === total ? `${total}` : `${sig.required} to ${total}`;
  throw new ModelError(`'${name}' expects ${expected} argument(s), got ${got}`);
}

/** A call's arguments against a signature, each omitted trailing optional
 * filled with the `undefined` that parameter's own union carries. */
function walkArgs(
  args: readonly ts.Expression[],
  sig: FnSig,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr[] {
  return sig.params.map((ty, i): EmitExpr => {
    const a = args[i];
    return a === undefined
      ? { kind: "inject", tag: "undefined" }
      : walkTyped(a, ty, scope, sf);
  });
}

/** What a use of a class needs to know: its fields in declaration order,
 * the getters that modeled, and its constructor's signature. */
export interface ClassShape {
  fields: string[];
  getters: ReadonlySet<string>;
  ctorParams: CtorValueTy[];
  /** The constructor parameters' source spellings, positionally aligned
   * with `ctorParams`. A class binder quantifies over them by name. */
  ctorParamNames: string[];
  /** Modeled methods by name, with their signatures. */
  methods: ReadonlyMap<string, FnSig>;
}

/** A binder's denoted domain: a finite half-open integer range, the whole
 * int line, the naturals, or a `number` binder — the whole double line,
 * narrowed by whichever bounds its interval carries. The same shapes the
 * old grammar's binder constructors carry. */
export type EmitBinder =
  | { name: string; kind: "range"; lo: string; hi: string }
  | { name: string; kind: "int" }
  | { name: string; kind: "nat" }
  | { name: string; kind: "number"; lower?: FloatBound; upper?: FloatBound }
  | {
      name: string;
      kind: "class";
      className: string;
      module?: string;
      ctorParams: EmitCtorParam[];
    };

/** One constructor parameter of a class binder's class. A class-typed one
 * carries its own parameters, so the tree bottoms out in numbers. */
export type EmitCtorParam =
  | { name: string; kind: "number" }
  | {
      name: string;
      kind: "class";
      className: string;
      module?: string;
      ctorParams: EmitCtorParam[];
    };

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

/** A member call on a freshly built instance. */
function instanceCall(
  e: ts.Expression,
):
  | { object: ts.NewExpression; name: string; args: readonly ts.Expression[] }
  | undefined {
  if (!ts.isCallExpression(e)) return undefined;
  const callee = e.expression;
  if (!ts.isPropertyAccessExpression(callee)) return undefined;
  const object = newCall(callee.expression);
  if (object === undefined) return undefined;
  if (!ts.isIdentifier(callee.name)) return undefined;
  return { object, name: callee.name.text, args: e.arguments };
}

/** A member access on a class-typed identifier: `p.x`, `p.g`. */
function varAccess(
  e: ts.Expression,
  scope: WalkScope,
): { ref: ModelRef; object: string; name: string } | undefined {
  if (!ts.isPropertyAccessExpression(e)) return undefined;
  const obj = unwrapParens(e.expression);
  if (!ts.isIdentifier(obj)) return undefined;
  const ty = scope.vars.get(obj.text);
  // A union-typed identifier has no members: the domain holds values, not
  // shapes, so a member read of one is not this access.
  if (ty === undefined || ty === "num" || "union" in ty) return undefined;
  if (!ts.isIdentifier(e.name)) return undefined;
  return { ref: ty.instance, object: obj.text, name: e.name.text };
}

/** A method call on a class-typed identifier: `p.m(args)`. */
function varCall(
  e: ts.Expression,
  scope: WalkScope,
):
  | {
      ref: ModelRef;
      object: string;
      name: string;
      args: readonly ts.Expression[];
    }
  | undefined {
  if (!ts.isCallExpression(e)) return undefined;
  const callee = e.expression;
  if (!ts.isPropertyAccessExpression(callee)) return undefined;
  const access = varAccess(callee, scope);
  return access === undefined ? undefined : { ...access, args: e.arguments };
}

/** A `this.m(...)` call: the only method call a member body can make. */
function thisCall(
  e: ts.Expression,
): { name: string; args: readonly ts.Expression[] } | undefined {
  if (!ts.isCallExpression(e)) return undefined;
  const callee = e.expression;
  if (!isThisAccess(callee)) return undefined;
  return { name: callee.name.text, args: e.arguments };
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
  if (ts.isIdentifier(u)) {
    // A bound identifier's recorded type is authoritative; an unbound
    // one stays permissive so it travels its own failure downstream.
    const ty = scope.vars.get(u.text);
    return ty === undefined || ty === "num";
  }
  if (isUnaryArith(u)) return true;
  // A conditional has no shape of its own: it is whatever both arms are.
  if (ts.isConditionalExpression(u))
    return (
      numericShaped(u.whenTrue, scope) && numericShaped(u.whenFalse, scope)
    );
  if (ts.isBinaryExpression(u))
    return ARITH_OPERATORS.has(u.operatorToken.getText());
  if (isThisAccess(u) || instanceAccess(u) !== undefined) return true;
  if (instanceCall(u) !== undefined || thisCall(u) !== undefined) return true;
  if (varAccess(u, scope) !== undefined || varCall(u, scope) !== undefined)
    return true;
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
  // A conditional has no shape of its own: it is whatever both arms are.
  if (ts.isConditionalExpression(u))
    return (
      booleanShaped(u.whenTrue, scope) && booleanShaped(u.whenFalse, scope)
    );
  if (builtinCall(u, scope)?.ty === "bool") return true;
  return equationSides(u) !== undefined;
}

/** What `typeof` can answer. */
const TYPEOF_RESULTS = new Set([
  "number",
  "string",
  "bigint",
  "boolean",
  "undefined",
  "object",
  "function",
  "symbol",
]);

/** `typeof v === "lit"` / `!==`, either side order, `v` an identifier:
 * the one typeof shape the model reads. Shape only — validity (a
 * union-typed operand, a recognized literal) is the walk's question. */
function typeofTest(e: ts.BinaryExpression):
  | {
      typeofNode: ts.TypeOfExpression;
      operand: ts.Identifier;
      result: string;
      negated: boolean;
    }
  | undefined {
  const op = e.operatorToken.getText();
  if (op !== "===" && op !== "!==") return undefined;
  const pick = (a: ts.Expression, b: ts.Expression) => {
    const t = unwrapParens(a);
    if (!ts.isTypeOfExpression(t)) return undefined;
    const operand = unwrapParens(t.expression);
    if (!ts.isIdentifier(operand)) return undefined;
    const lit = unwrapParens(b);
    if (!ts.isStringLiteral(lit)) return undefined;
    return { typeofNode: t, operand, result: lit.text };
  };
  const found = pick(e.left, e.right) ?? pick(e.right, e.left);
  return found === undefined ? undefined : { ...found, negated: op === "!==" };
}

/** Whether a recognized typeof-test shape is inside the model: the
 * operand is union-typed and the literal is a typeof result. */
function validTypeofTest(
  tt: { operand: ts.Identifier; result: string },
  scope: WalkScope,
): boolean {
  const bound = scope.vars.get(tt.operand.text);
  return (
    bound !== undefined &&
    typeof bound !== "string" &&
    "union" in bound &&
    TYPEOF_RESULTS.has(tt.result)
  );
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
  // `null` is an expression atom for the union positions; whether a
  // position admits it is the typed walk's question, and elsewhere it
  // degrades there with this same construct.
  if (e.kind === ts.SyntaxKind.NullKeyword) return undefined;
  if (negatedLiteral(e) !== undefined) return undefined;
  if (isUnaryArith(e)) return findConstruct(e.operand, sf, scope);
  if (ts.isBinaryExpression(e)) {
    const tt = typeofTest(e);
    if (tt !== undefined) {
      if (validTypeofTest(tt, scope)) return undefined;
      return constructAt(tt.typeofNode, tt.typeofNode.kind, sf);
    }
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
  if (ts.isConditionalExpression(e)) {
    if (!booleanShaped(e.condition, scope))
      return nonBooleanOperand("?:", "the condition", e.condition, sf);
    return (
      findConstruct(e.condition, sf, scope) ??
      findConstruct(e.whenTrue, sf, scope) ??
      findConstruct(e.whenFalse, sf, scope)
    );
  }
  const sides = equationSides(e);
  if (sides !== undefined) {
    // `Object.is` compares JS values; the model holds numbers plus the
    // tags JsVal carries — booleans, union values, `undefined`, `null` —
    // and SameValue is total over any mix of them (cross-tag is false).
    // An argument outside those — a string, an instance — is refused on
    // the merits.
    const admits = (s: ts.Expression) =>
      numericShaped(s, scope) || taggedOperand(s, scope);
    const offender = sides.findIndex((s) => !admits(s));
    if (offender !== -1) {
      const arg = unwrapParens(sides[offender]!);
      const { line, character } = sf.getLineAndCharacterOfPosition(
        arg.getStart(sf),
      );
      const at = `(${kindName(arg.kind)} at ${line + 1}:${character + 1})`;
      return {
        construct: "Object.is",
        reason:
          `'Object.is' admits numbers, booleans, union values, ` +
          `'undefined', and 'null'; argument ${offender + 1} is not one ${at}`,
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
  // A this-call is shaped on the same condition as the field read above.
  if (scope.self !== undefined) {
    const selfCall = thisCall(e);
    if (selfCall !== undefined) {
      for (const a of selfCall.args) {
        const found = findConstruct(a, sf, scope);
        if (found !== undefined) return found;
      }
      return undefined;
    }
  }
  const icall = instanceCall(e);
  if (icall !== undefined) {
    const found = findConstruct(icall.object, sf, scope);
    if (found !== undefined) return found;
    for (const a of icall.args) {
      const inner = findConstruct(a, sf, scope);
      if (inner !== undefined) return inner;
    }
    return undefined;
  }
  const access = instanceAccess(e);
  if (access !== undefined) return findConstruct(access.object, sf, scope);
  // A class-typed identifier's member read or call is shaped; its object
  // is an identifier, so only the arguments carry constructs.
  const vcall = varCall(e, scope);
  if (vcall !== undefined) {
    for (const a of vcall.args) {
      const found = findConstruct(a, sf, scope);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  if (varAccess(e, scope) !== undefined) return undefined;
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
  if (ts.isConditionalExpression(e)) {
    return (
      findRefusedOp(e.condition) ??
      findRefusedOp(e.whenTrue) ??
      findRefusedOp(e.whenFalse)
    );
  }
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText();
    const reason = REFUSED_OPERATORS.get(op);
    if (reason !== undefined) return { construct: op, reason };
    return findRefusedOp(e.left) ?? findRefusedOp(e.right);
  }
  const icall = instanceCall(e);
  if (icall !== undefined) {
    const found = findRefusedOp(icall.object);
    if (found !== undefined) return found;
    for (const a of icall.args) {
      const inner = findRefusedOp(a);
      if (inner !== undefined) return inner;
    }
    return undefined;
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
  if (ts.isConditionalExpression(e)) {
    callNames(e.condition, scope, into);
    callNames(e.whenTrue, scope, into);
    return callNames(e.whenFalse, scope, into);
  }
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
  const icall = instanceCall(e);
  if (icall !== undefined) {
    callNames(icall.object, scope, into);
    for (const a of icall.args) callNames(a, scope, into);
    return into;
  }
  const selfCall = thisCall(e);
  if (selfCall !== undefined) {
    for (const a of selfCall.args) callNames(a, scope, into);
    return into;
  }
  const access = instanceAccess(e);
  if (access !== undefined) return callNames(access.object, scope, into);
  const vcall = varCall(e, scope);
  if (vcall !== undefined) {
    // The receiver is a bound name, not a callee; the arguments carry them.
    for (const a of vcall.args) callNames(a, scope, into);
    return into;
  }
  if (varAccess(e, scope) !== undefined) return into;
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
  vars: ReadonlyMap<string, ValueTy>;
  mapped: ReadonlyMap<string, FnSig>;
  failed: ReadonlyMap<string, FailedDecl>;
  classes: ReadonlyMap<string, ClassShape>;
  /** Module-level constants the model admits, by model key. */
  constants: ReadonlySet<string>;
  /** Module-level aliases of whitelisted builtins, by model key. */
  aliases: ReadonlyMap<string, BuiltinEntry>;
  /** Source spellings this module binds elsewhere: imported names, and
   * only those. A spelling absent here is this module's own. */
  names: ReadonlyMap<string, ModelRef>;
  /** This module's qualifier; empty for the entry file. */
  module: string;
  /** Set inside a getter body, where `this` denotes the instance. */
  self?: { ref: ModelRef; shape: ClassShape };
  /** Set inside a member body: the enclosing class's member failures,
   * live while the class is still being walked. */
  selfFailed?: ReadonlyMap<string, FailedDecl>;
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
function travelFrom(
  failedMap: ReadonlyMap<string, FailedDecl>,
  ref: ModelRef,
): FailedDecl | undefined {
  const failed = failedMap.get(modelKey(ref));
  if (failed?.construct === undefined) return undefined;
  return {
    construct: failed.construct,
    reason: `'${displayName(ref)}' could not be modeled: ${failed.reason}`,
  };
}

function travelFailure(
  scope: WalkScope,
  ref: ModelRef,
): FailedDecl | undefined {
  return travelFrom(scope.failed, ref);
}

/** The shape and failure registry a class ref resolves against: the
 * closure's for a registered class, the walk-in-progress ones when the
 * ref names the class currently being walked. */
function classView(
  scope: WalkScope,
  ref: ModelRef,
): { shape: ClassShape; failed: ReadonlyMap<string, FailedDecl> } | undefined {
  const registered = scope.classes.get(modelKey(ref));
  if (registered !== undefined)
    return { shape: registered, failed: scope.failed };
  const self = scope.self;
  /* v8 ignore start -- a bound name is class-typed only at a registered
     class or the enclosing one; every other spelling degrades its
     declaration before the body that would read off it is walked. */
  if (
    self === undefined ||
    scope.selfFailed === undefined ||
    modelKey(ref) !== modelKey(self.ref)
  ) {
    return undefined;
  }
  /* v8 ignore stop */
  return { shape: self.shape, failed: scope.selfFailed };
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
  if (ts.isConditionalExpression(e)) {
    return (
      findFailedMemberUse(e.condition, scope) ??
      findFailedMemberUse(e.whenTrue, scope) ??
      findFailedMemberUse(e.whenFalse, scope)
    );
  }
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
  const selfCall = thisCall(e);
  if (selfCall !== undefined && scope.self !== undefined) {
    // The live registry holds only already-walked siblings, so a forward
    // call still falls to the typed walk, as source order demands.
    if (
      scope.selfFailed !== undefined &&
      !scope.self.shape.methods.has(selfCall.name)
    ) {
      const travelled = travelFrom(scope.selfFailed, {
        module: scope.self.ref.module,
        name: qualifiedName(selfCall.name, scope.self.ref.name),
      });
      if (travelled !== undefined) return travelled;
    }
    for (const a of selfCall.args) {
      const found = findFailedMemberUse(a, scope);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  const icall = instanceCall(e);
  if (icall !== undefined) {
    const found = findFailedMemberUse(icall.object, scope);
    if (found !== undefined) return found;
    const ref = newRef(scope, icall.object);
    const shape = scope.classes.get(modelKey(ref));
    // An unmodeled class already travelled through its own `new`.
    if (shape !== undefined && !shape.methods.has(icall.name)) {
      const travelled = travelFailure(scope, {
        module: ref.module,
        name: qualifiedName(icall.name, ref.name),
      });
      if (travelled !== undefined) return travelled;
    }
    for (const a of icall.args) {
      const inner = findFailedMemberUse(a, scope);
      if (inner !== undefined) return inner;
    }
    return undefined;
  }
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
  const vcall = varCall(e, scope);
  if (vcall !== undefined) {
    const view = classView(scope, vcall.ref);
    if (view !== undefined && !view.shape.methods.has(vcall.name)) {
      const travelled = travelFrom(view.failed, {
        module: vcall.ref.module,
        name: qualifiedName(vcall.name, vcall.ref.name),
      });
      if (travelled !== undefined) return travelled;
    }
    for (const a of vcall.args) {
      const inner = findFailedMemberUse(a, scope);
      if (inner !== undefined) return inner;
    }
    return undefined;
  }
  const vaccess = varAccess(e, scope);
  if (vaccess !== undefined) {
    const view = classView(scope, vaccess.ref);
    if (view === undefined) return undefined;
    if (
      view.shape.getters.has(vaccess.name) ||
      view.shape.fields.includes(vaccess.name)
    ) {
      return undefined;
    }
    return travelFrom(view.failed, {
      module: vaccess.ref.module,
      name: qualifiedName(vaccess.name, vaccess.ref.name),
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

type Expected = ValueTy | "bool";

function describeTy(t: Expected): string {
  if (t === "num") return "a number";
  if (t === "bool") return "a boolean";
  if ("union" in t) return `a '${t.union.join(" | ")}' value`;
  return `an instance of '${displayName(t.instance)}'`;
}

/** An engine-route failure: the walk found something with no model, or a
 * type mismatch — the failures the old pipeline reports as `Error`. A
 * construct rides along when the failure travels from a declaration the
 * input itself degraded, keeping the classification `Inappropriate`
 * through every catch that wraps the walk. */
class ModelError extends Error {
  constructor(
    reason: string,
    readonly construct?: string,
  ) {
    super(reason);
  }
}

/** A caught walk failure as a `FailedDecl`, construct preserved. */
function modelFailure(err: ModelError): FailedDecl {
  return err.construct !== undefined
    ? { construct: err.construct, reason: err.message }
    : { reason: err.message };
}

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

/** The shape behind a class-typed identifier: the enclosing class's own,
 * which the registries do not carry until its walk ends, or an earlier
 * class's. Going through the same shapes the walk already consults is
 * what inherits the source-order discipline rather than restating it. */
function shapeOfRef(scope: WalkScope, ref: ModelRef): ClassShape {
  if (scope.self !== undefined && sameClass(ref, scope.self.ref))
    return scope.self.shape;
  return classShapeOf(scope, ref);
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
  if (isUnionTy(expected)) return walkUnionSlot(e, expected.union, scope, sf);
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
    const bound = scope.vars.get(e.text);
    const constRef = bound === undefined ? refOf(scope, e.text) : undefined;
    const constant =
      constRef !== undefined && scope.constants.has(modelKey(constRef));
    const global =
      bound === undefined &&
      !constant &&
      GLOBAL_NUMBER_ATOMS.has(e.text) &&
      !moduleBinds(scope, e.text);
    if (bound === undefined && !constant && !global) {
      // A value-position read of a module binding travels the
      // declaration's own failure, exactly as a call through one does.
      const ref = refOf(scope, e.text);
      const alias = scope.aliases.get(modelKey(ref));
      if (alias !== undefined) {
        throw new ModelError(
          `'${e.text}' aliases '${alias.name}', which is modeled only ` +
            `as a callee`,
          alias.name,
        );
      }
      const travel = travelFailure(scope, ref);
      if (travel !== undefined) {
        throw new ModelError(travel.reason, travel.construct);
      }
      const failed = scope.failed.get(modelKey(ref));
      if (failed !== undefined) {
        throw new ModelError(
          `'${displayName(ref)}' has no model: ${failed.reason}`,
        );
      }
      throw new ModelError(`unbound identifier '${e.text}'`);
    }
    // The atoms and module constants are numbers; a bound name carries
    // whatever type it was bound at, and an instance matches only its
    // own class.
    const actual: ValueTy = bound ?? "num";
    // A union-typed read at a number position lowers as the throwing
    // projection; the norm layer discharges it on tag-determined paths.
    if (expected === "num" && typeof actual !== "string" && "union" in actual) {
      return {
        kind: "project",
        tag: "number",
        expr: { kind: "id", name: e.text },
      };
    }
    // A union `expected` never reaches here: the slot walk intercepted it.
    const ok =
      typeof expected === "string"
        ? expected === actual
        : typeof actual !== "string" &&
          "instance" in actual &&
          sameClass(actual.instance, expected.instance);
    if (!ok) {
      throw new ModelError(
        `identifier '${e.text}' is ${describeTy(actual)}, ` +
          `not ${describeTy(expected)}`,
      );
    }
    if (bound !== undefined) return { kind: "id", name: e.text };
    if (constant) {
      return {
        kind: "const-read",
        name: constRef!.name,
        ...(constRef!.module !== "" ? { module: constRef!.module } : {}),
      };
    }
    return { kind: "num", lit: e.text };
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
  if (ts.isConditionalExpression(e)) {
    // Both arms answer at the position's own type, so a conditional is
    // whatever type its context asks for; only the condition is pinned.
    const cond = walkTyped(e.condition, "bool", scope, sf);
    const whenTrue = walkTyped(e.whenTrue, expected, scope, sf);
    const whenFalse = walkTyped(e.whenFalse, expected, scope, sf);
    return { kind: "cond", cond, then: whenTrue, else: whenFalse };
  }
  if (ts.isBinaryExpression(e)) {
    const tt = typeofTest(e);
    if (tt !== undefined) {
      /* v8 ignore start -- the construct scan admits only valid tests, so
         an invalid one degraded the declaration before the walk; the
         throw mirrors the scan for the same defense. */
      if (!validTypeofTest(tt, scope)) {
        const failed = constructAt(tt.typeofNode, tt.typeofNode.kind, sf);
        throw new ModelError(failed.reason, failed.construct);
      }
      /* v8 ignore stop */
      if (expected !== "bool") {
        throw new ModelError(
          `a 'typeof' test yields a boolean, not ${describeTy(expected)}`,
        );
      }
      const test: EmitExpr = {
        kind: "typeof-test",
        expr: { kind: "id", name: tt.operand.text },
        result: tt.result,
      };
      return tt.negated ? { kind: "unop", op: "!", operand: test } : test;
    }
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
    if (op === "===" || op === "!==") {
      const eq = unionEquality(e.left, e.right, "strict", scope, sf);
      if (eq !== undefined) {
        if (expected !== "bool") {
          throw new ModelError(
            `operator '${op}' yields a boolean, not ${describeTy(expected)}`,
          );
        }
        return op === "===" ? eq : { kind: "unop", op: "!", operand: eq };
      }
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
    // else is outside the model, and the operator is the construct.
    const refused = REFUSED_OPERATORS.get(op);
    if (refused !== undefined) throw new ModelError(refused);
    throw new ModelError(`operator '${op}' has no model in this slice`, op);
  }
  const sides = equationSides(e);
  if (sides !== undefined) {
    const sv = unionEquality(sides[0], sides[1], "same-value", scope, sf);
    if (sv !== undefined) {
      if (expected !== "bool") {
        throw new ModelError(
          `a call to 'Object.is' yields a boolean, not ${describeTy(expected)}`,
        );
      }
      return sv;
    }
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
  if (scope.self !== undefined) {
    const selfCall = thisCall(e);
    if (selfCall !== undefined) {
      const sig = scope.self.shape.methods.get(selfCall.name);
      if (sig === undefined) {
        throw new ModelError(
          `'this.${selfCall.name}' does not name a modeled method of ` +
            `'${scope.self.ref.name}'`,
        );
      }
      checkArity(
        qualifiedName(selfCall.name, scope.self.ref.name),
        sig,
        selfCall.args.length,
      );
      /* v8 ignore start -- no boolean position admits a method call:
         every one of them is gated on `booleanShaped`, which a call on
         `this` is not. The throw mirrors the field read's. */
      if (expected !== "num") {
        throw new ModelError(
          `a method call yields a number, not ${describeTy(expected)}`,
        );
      }
      /* v8 ignore stop */
      return {
        kind: "method-call",
        className: scope.self.ref.name,
        ...(scope.self.ref.module !== ""
          ? { module: scope.self.ref.module }
          : {}),
        name: selfCall.name,
        object: { kind: "self" },
        args: walkArgs(selfCall.args, sig, scope, sf),
      };
    }
  }
  const icall = instanceCall(e);
  if (icall !== undefined) {
    const ref = newRef(scope, icall.object);
    const shape = classShapeOf(scope, ref);
    const rawCtorArgs = icall.object.arguments ?? [];
    if (shape.ctorParams.length !== rawCtorArgs.length) {
      throw new ModelError(
        `'${displayName(ref)}' expects ${shape.ctorParams.length} ` +
          `argument(s), got ${rawCtorArgs.length}`,
      );
    }
    const sig = shape.methods.get(icall.name);
    if (sig === undefined) {
      throw new ModelError(
        `'${displayName(ref)}' has no method '${icall.name}' in the model`,
      );
    }
    checkArity(qualifiedName(icall.name, ref.name), sig, icall.args.length);
    /* v8 ignore start -- as above: `booleanShaped` admits no call on a
       fresh instance, so no boolean position reaches this. */
    if (expected !== "num") {
      throw new ModelError(
        `a method call yields a number, not ${describeTy(expected)}`,
      );
    }
    /* v8 ignore stop */
    const module = ref.module !== "" ? { module: ref.module } : {};
    const object: EmitExpr = {
      kind: "new",
      className: ref.name,
      ...module,
      args: rawCtorArgs.map((a, i) =>
        walkTyped(a, shape.ctorParams[i]!, scope, sf),
      ),
    };
    return {
      kind: "method-call",
      className: ref.name,
      ...module,
      name: icall.name,
      object,
      args: walkArgs(icall.args, sig, scope, sf),
    };
  }
  const access = instanceAccess(e);
  if (access !== undefined) {
    const ref = newRef(scope, access.object);
    const shape = classShapeOf(scope, ref);
    const rawArgs = access.object.arguments ?? [];
    if (shape.ctorParams.length !== rawArgs.length) {
      throw new ModelError(
        `'${displayName(ref)}' expects ${shape.ctorParams.length} ` +
          `argument(s), got ${rawArgs.length}`,
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
      args: rawArgs.map((a, i) =>
        walkTyped(a, shape.ctorParams[i]!, scope, sf),
      ),
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
  const vcall = varCall(e, scope);
  if (vcall !== undefined) {
    const shape = shapeOfRef(scope, vcall.ref);
    const sig = shape.methods.get(vcall.name);
    if (sig === undefined) {
      throw new ModelError(
        `'${displayName(vcall.ref)}' has no method '${vcall.name}' in the model`,
      );
    }
    checkArity(
      qualifiedName(vcall.name, vcall.ref.name),
      sig,
      vcall.args.length,
    );
    /* v8 ignore start -- as for the calls on a fresh instance:
       `booleanShaped` admits no method call, so no boolean position
       reaches this. The throw is kept for the same defense. */
    if (expected !== "num") {
      throw new ModelError(
        `a method call yields a number, not ${describeTy(expected)}`,
      );
    }
    /* v8 ignore stop */
    return {
      kind: "method-call",
      className: vcall.ref.name,
      ...(vcall.ref.module !== "" ? { module: vcall.ref.module } : {}),
      name: vcall.name,
      object: { kind: "id", name: vcall.object },
      args: walkArgs(vcall.args, sig, scope, sf),
    };
  }
  const vaccess = varAccess(e, scope);
  if (vaccess !== undefined) {
    const shape = shapeOfRef(scope, vaccess.ref);
    /* v8 ignore start -- a bound name is class-typed only inside a body,
       whose only boolean position is a branch condition, and
       `booleanShaped` admits no member read. */
    if (expected !== "num") {
      throw new ModelError(
        `a member read yields a number, not ${describeTy(expected)}`,
      );
    }
    /* v8 ignore stop */
    const module =
      vaccess.ref.module !== "" ? { module: vaccess.ref.module } : {};
    const object: EmitExpr = { kind: "id", name: vaccess.object };
    if (shape.getters.has(vaccess.name)) {
      return {
        kind: "getter-read",
        className: vaccess.ref.name,
        ...module,
        name: vaccess.name,
        object,
      };
    }
    if (shape.fields.includes(vaccess.name)) {
      return {
        kind: "field-read",
        className: vaccess.ref.name,
        ...module,
        field: vaccess.name,
        object,
      };
    }
    throw new ModelError(
      `'${displayName(vaccess.ref)}' has no member '${vaccess.name}' in the model`,
    );
  }
  const built = newCall(e);
  if (built !== undefined) {
    const ref = newRef(scope, built);
    // The class must exist before the instance is admitted or refused.
    const shape = classShapeOf(scope, ref);
    if (typeof expected !== "string" && sameClass(ref, expected.instance)) {
      const rawArgs = built.arguments ?? [];
      if (shape.ctorParams.length !== rawArgs.length) {
        throw new ModelError(
          `'${displayName(ref)}' expects ${shape.ctorParams.length} ` +
            `argument(s), got ${rawArgs.length}`,
        );
      }
      return {
        kind: "new",
        className: ref.name,
        ...(ref.module !== "" ? { module: ref.module } : {}),
        args: rawArgs.map((a, i) =>
          walkTyped(a, shape.ctorParams[i]!, scope, sf),
        ),
      };
    }
    throw new ModelError(
      `'new ${displayName(ref)}(...)' yields an instance of ` +
        `'${displayName(ref)}', not ${describeTy(expected)}`,
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
    if (!scope.vars.has(e.expression.text)) {
      if (scope.constants.has(key)) {
        throw new ModelError(`'${name}' is a constant; it cannot be called`);
      }
      // An arity-1 alias call was claimed as the builtin above; whatever
      // alias call survives to here misuses it, exactly as a stray use
      // of the direct spelling would.
      if (scope.aliases.has(key)) {
        const misuse = constructAt(e, e.kind, sf);
        throw new ModelError(misuse.reason, misuse.construct);
      }
    }
    const sig = scope.mapped.get(key);
    if (sig === undefined) {
      const failed = scope.failed.get(key);
      if (failed !== undefined) {
        throw new ModelError(`'${name}' has no model: ${failed.reason}`);
      }
      throw new ModelError(`no model registered for '${name}'`);
    }
    checkArity(name, sig, e.arguments.length);
    if (expected !== "num") {
      throw new ModelError(
        `a call to '${name}' yields a number, not ${describeTy(expected)}`,
      );
    }
    const args = walkArgs(e.arguments, sig, scope, sf);
    return {
      kind: "call",
      callee: ref.name,
      ...(ref.module !== "" ? { module: ref.module } : {}),
      args,
    };
  }
  // `null` is admitted by the construct scan for the union positions; at
  // any other position it degrades exactly as the scan used to degrade it.
  if (e.kind === ts.SyntaxKind.NullKeyword) {
    const failed = constructAt(e, e.kind, sf);
    throw new ModelError(failed.reason, failed.construct);
  }
  // Unreachable after the construct scan; degrade like an opaque node.
  throw new ModelError(constructAt(e, e.kind, sf).reason);
}

/** Whether an expression is a union-typed identifier in scope. */
function unionIdent(e: ts.Expression, scope: WalkScope): boolean {
  const u = unwrapParens(e);
  if (!ts.isIdentifier(u)) return false;
  const ty = scope.vars.get(u.text);
  return ty !== undefined && typeof ty !== "string" && "union" in ty;
}

/** `undefined` as JS resolves it here: the global, unshadowed. */
function undefAtom(e: ts.Expression, scope: WalkScope): boolean {
  const u = unwrapParens(e);
  return (
    ts.isIdentifier(u) &&
    u.text === "undefined" &&
    !scope.vars.has(u.text) &&
    !scope.constants.has(modelKey(refOf(scope, u.text))) &&
    !moduleBinds(scope, u.text)
  );
}

/** Whether an equality operand pulls the comparison into the tagged
 * domain: a union-typed identifier, a boolean-valued shape, or the
 * `undefined`/`null` atoms — every static tag JsVal carries beyond the
 * numbers-only slice. String and bigint values have no expression forms
 * here, so no operand reaches those tags. */
function taggedOperand(e: ts.Expression, scope: WalkScope): boolean {
  const u = unwrapParens(e);
  return (
    unionIdent(u, scope) ||
    booleanShaped(u, scope) ||
    undefAtom(u, scope) ||
    u.kind === ts.SyntaxKind.NullKeyword
  );
}

/** One side of a JsVal equality: a union identifier stays itself, the
 * undefined/null atoms inject at their tags, a boolean-valued shape
 * injects at 'boolean', and everything else is a number injected at
 * its. */
function eqOperand(
  e: ts.Expression,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  const u = unwrapParens(e);
  if (unionIdent(u, scope))
    return { kind: "id", name: (u as ts.Identifier).text };
  if (undefAtom(u, scope)) return { kind: "inject", tag: "undefined" };
  if (u.kind === ts.SyntaxKind.NullKeyword)
    return { kind: "inject", tag: "null" };
  if (booleanShaped(u, scope))
    return {
      kind: "inject",
      tag: "boolean",
      expr: walkTyped(u, "bool", scope, sf),
    };
  return {
    kind: "inject",
    tag: "number",
    expr: walkTyped(u, "num", scope, sf),
  };
}

/** An equality pulled into the tagged domain, undefined when no operand
 * pulls it there, leaving the number path in place. `===`/`!==` lower
 * over JsVal when an operand is union-typed; `Object.is` also when one
 * is any other tagged shape — SameValue is total over the domain, so a
 * statically cross-tag pair evaluates false instead of refusing. */
function unionEquality(
  l: ts.Expression,
  r: ts.Expression,
  semantics: "strict" | "same-value",
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr | undefined {
  const pulls = semantics === "same-value" ? taggedOperand : unionIdent;
  if (!pulls(l, scope) && !pulls(r, scope)) return undefined;
  return {
    kind: "jsval-eq",
    semantics,
    left: eqOperand(l, scope, sf),
    right: eqOperand(r, scope, sf),
  };
}

/** An expression meeting a union slot. An identical-union identifier
 * flows as itself; the `undefined`/`null` atoms inject where the union
 * carries their tag (any binding of those spellings shadows, exactly as
 * `NaN`/`Infinity` behave); anything that walks at `num` injects at
 * `number`. Union subtyping is out of scope: a narrower, wider, or
 * overlapping union refuses. */
function walkUnionSlot(
  e: ts.Expression,
  union: UnionTag[],
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  const u = unwrapParens(e);
  if (ts.isIdentifier(u)) {
    const bound = scope.vars.get(u.text);
    if (bound !== undefined && typeof bound !== "string" && "union" in bound) {
      if (sameUnion(bound.union, union)) return { kind: "id", name: u.text };
      throw new ModelError(
        `identifier '${u.text}' is ${describeTy(bound)}, not ` +
          `${describeTy({ union })}; unions flow only between identical spellings`,
      );
    }
    if (
      bound === undefined &&
      u.text === "undefined" &&
      union.includes("undefined") &&
      !scope.constants.has(modelKey(refOf(scope, u.text))) &&
      !moduleBinds(scope, u.text)
    ) {
      return { kind: "inject", tag: "undefined" };
    }
  }
  if (u.kind === ts.SyntaxKind.NullKeyword) {
    if (union.includes("null")) return { kind: "inject", tag: "null" };
    const failed = constructAt(u, u.kind, sf);
    throw new ModelError(failed.reason, failed.construct);
  }
  if (!union.includes("number")) {
    throw new ModelError(
      `${describeTy({ union })} slot has no 'number' member, so a ` +
        `number-valued expression cannot flow to it`,
    );
  }
  return {
    kind: "inject",
    tag: "number",
    expr: walkTyped(u, "num", scope, sf),
  };
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
    if (err instanceof ModelError) return modelFailure(err);
    throw err;
  }
}

/** The signature check `transcribeFunction` applies: the walked
 * parameters, or the failure that degrades the function. */
function signatureFailure(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
  reg: ParamReg,
): { params: WalkedParams } | FailedDecl {
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
  const params = walkParams(fn.parameters, sf, reg, fnParamFailure);
  if (!Array.isArray(params)) return params;
  if (fn.type === undefined || fn.body === undefined)
    return constructAt(fn, fn.kind, sf);
  if (fn.type.kind !== ts.SyntaxKind.NumberKeyword)
    return constructAt(fn.type, fn.type.kind, sf);
  return { params };
}

/** Names a body binds itself, and whether each may be assigned — the old
 * transcriber's `Locals`, with the same discipline: a branch's arm gets
 * its own copy, and a redeclaration of a name from an enclosing scope is
 * refused rather than shadowed. */
type Locals = Map<string, "const" | "mutable">;

/** The types a local binding may carry: the numeric slice, or a keyword
 * union riding the same tagged domain a parameter's does. Instances stay
 * out: a class-valued local keeps its refusal. */
type LocalTy = "num" | { union: UnionTag[] };

/** The statement tree as the old transcriber would have rendered it: each
 * node is either a mapped statement (its expressions still tsc nodes) or
 * the opaque failure the transcriber would have emitted in its place. */
type TStmt =
  | { t: "return"; expr: ts.Expression }
  | { t: "throw"; error: string }
  | {
      t: "decl";
      mutable: boolean;
      name: string;
      init: ts.Expression;
      ty: LocalTy;
    }
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

/** A local declarator's admitted type: the numeric slice for `number` or
 * no annotation, or a keyword union normalized exactly as a parameter's
 * is (`localValueTy` and `paramValueTy` share `keywordTags` and
 * `normalizedUnion`, so the two spellings can never drift). Anything
 * else — a class, a lone non-number keyword, a union with a member
 * outside the keywords — keeps the declarator's degradation. */
function localValueTy(
  t: ts.TypeNode | undefined,
  sf: ts.SourceFile,
): LocalTy | undefined {
  if (t === undefined || t.kind === ts.SyntaxKind.NumberKeyword) return "num";
  if (!ts.isUnionTypeNode(t)) return undefined;
  const tags = keywordTags(t);
  if (!Array.isArray(tags)) return undefined;
  const ty = normalizedUnion(tags, t, sf);
  return typeof ty === "string" || "union" in ty ? ty : undefined;
}

/** A declaration's `TStmt`s, or undefined when any declarator falls
 * outside the slice — `var`, `using`, destructuring, an uninitialized
 * `let`, a type annotation that is neither `number` nor a keyword union,
 * or a redeclaration of a name already bound here. Locals set for
 * earlier declarators persist even when a later one fails, exactly as
 * the old transcriber leaves them. */
function declStmts(
  s: ts.VariableStatement,
  locals: Locals,
  sf: ts.SourceFile,
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
    const ty = localValueTy(d.type, sf);
    if (ty === undefined) return undefined;
    // Shadowing a name already bound here would make a join ambiguous: an
    // arm's own binding is what the tail would read back.
    if (locals.has(d.name.text)) return undefined;
    stmts.push({
      t: "decl",
      mutable: !isConst,
      name: d.name.text,
      init: d.initializer,
      ty,
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
    const stmts = declStmts(s, locals, sf);
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
 * expression — whichever the old pipeline's scan reaches first. Each decl
 * binds the rest of its list — an arm its own copy — mirroring the
 * lowering's scoping, so the scan types an identifier (a typeof test over
 * a union local, say) off the same binding the walk will. */
function treeConstruct(
  stmts: readonly TStmt[],
  sf: ts.SourceFile,
  scope: WalkScope,
): FailedDecl | undefined {
  let current = scope;
  for (const s of stmts) {
    switch (s.t) {
      case "opaque":
        return s.failure;
      case "return": {
        const found = findConstruct(s.expr, sf, current);
        if (found !== undefined) return found;
        break;
      }
      case "decl": {
        const found = findConstruct(s.init, sf, current);
        if (found !== undefined) return found;
        const vars = new Map(current.vars);
        vars.set(s.name, s.ty);
        current = { ...current, vars };
        break;
      }
      case "assign":
      case "field-set": {
        const found = findConstruct(s.expr, sf, current);
        if (found !== undefined) return found;
        break;
      }
      case "if": {
        if ("opaque" in s.cond) return s.cond.opaque;
        const found =
          findConstruct(s.cond.expr, sf, current) ??
          treeConstruct(s.then, sf, current) ??
          (s.else !== undefined
            ? treeConstruct(s.else, sf, current)
            : undefined);
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
  vars: readonly (readonly [string, ValueTy])[],
  k: Cont,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitStmt[] {
  const walk = (
    e: ts.Expression,
    expected: Expected,
    names: readonly (readonly [string, ValueTy])[],
  ) => walkTyped(e, expected, { ...scope, vars: new Map(names) }, sf);
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
      // a substitution, so an unused initializer still evaluates. A union
      // local's initializer meets its declared type as a slot, exactly as
      // an argument meets a union parameter's.
      const init = walk(s.init, s.ty, vars);
      const tail = lowerTree(
        rest,
        [...vars, [s.name, s.ty] as const],
        k,
        scope,
        sf,
      );
      return [
        {
          kind: s.mutable ? "let" : "const",
          name: s.name,
          init,
          ...(s.ty !== "num" ? { type: [...s.ty.union] } : {}),
        },
        ...tail,
      ];
    }
    case "assign": {
      // A reassignment is typed at what the target was bound at — a
      // parameter's or a union local's type included.
      const target = vars.find(([n]) => n === s.name)?.[1] ?? "num";
      const expr = walk(s.expr, target, vars);
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

/** The shape checks a parameter passes before its type is read: a
 * binding pattern, a rest, and a missing type annotation are all outside
 * the slice. An optional is admitted only where `optionals` says so —
 * call-site arity can fill one for a free function or a method, while a
 * constructor keeps the ban. */
function paramShapeFailure(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
  optionals: boolean,
): FailedDecl | undefined {
  if (!ts.isIdentifier(p.name)) return constructAt(p.name, p.name.kind, sf);
  if (p.dotDotDotToken !== undefined)
    return constructAt(p.dotDotDotToken, p.dotDotDotToken.kind, sf);
  if (p.questionToken !== undefined && !optionals)
    return constructAt(p, p.kind, sf);
  if (p.type === undefined) return constructAt(p, p.kind, sf);
  return undefined;
}

/** A free function's parameter additionally refuses a default; only the
 * class walks model defaulted parameters so far. */
function fnParamFailure(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  if (p.initializer !== undefined) return constructAt(p, p.kind, sf);
  return paramShapeFailure(p, sf, true);
}

/** A modifier on a member's parameter is a parameter property, which
 * declares a field the body never assigns. */
function memberParamModifier(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  const mods = ts.getModifiers(p) ?? [];
  return mods.length > 0 ? constructAt(mods[0]!, mods[0]!.kind, sf) : undefined;
}

/** A constructor parameter passes the shape check with defaults admitted
 * — every modeled `new` supplies full arity, so the initializer is dead
 * code — and optionals refused, there being no arity to fill them. */
function ctorParamFailure(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  return memberParamModifier(p, sf) ?? paramShapeFailure(p, sf, false);
}

/** A method's parameter takes optionals, its calls carrying the same
 * arity loosening a free function's do. */
function methodParamFailure(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
): FailedDecl | undefined {
  return memberParamModifier(p, sf) ?? paramShapeFailure(p, sf, true);
}

/** The registries a parameter's type resolves against — a `WalkScope`
 * before there is one. `self` is the class a member's parameter may name;
 * a constructor has none, its class not being modeled yet. */
interface ParamReg {
  classes: ReadonlyMap<string, ClassShape>;
  failed: ReadonlyMap<string, FailedDecl>;
  names: ReadonlyMap<string, ModelRef>;
  module: string;
  self?: ModelRef;
  /** Whether a union type is admitted here: free functions and methods
   * take them, a constructor keeps its refusal. */
  unions: boolean;
}

/** A parameter's declared type: a number, an already-modeled class, or
 * the failure that degrades the declaration. A class resolves under the
 * source-order discipline member calls follow, and one that degraded
 * travels its own failure, the way a call to it would. */
function paramValueTy(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
  reg: ParamReg,
): ValueTy | FailedDecl {
  const t = p.type!;
  // An optional's declared type is widened by `undefined`: the question
  // mark is arity, the union is the type. Only the keyword domain carries
  // that tag, so an optional at any other type refuses at the parameter,
  // exactly where the blanket optional ban used to refuse.
  if (p.questionToken !== undefined) {
    const tags = keywordTags(t);
    if (!Array.isArray(tags)) return constructAt(p, p.kind, sf);
    return normalizedUnion([...tags, "undefined"], t, sf);
  }
  if (t.kind === ts.SyntaxKind.NumberKeyword) return "num";
  if (
    ts.isTypeReferenceNode(t) &&
    ts.isIdentifier(t.typeName) &&
    t.typeArguments === undefined
  ) {
    const spelling = t.typeName.text;
    const ref = reg.names.get(spelling) ?? {
      module: reg.module,
      name: spelling,
    };
    if (reg.self !== undefined && sameClass(ref, reg.self))
      return { instance: ref };
    if (reg.classes.has(modelKey(ref))) return { instance: ref };
    const failed = reg.failed.get(modelKey(ref));
    if (failed !== undefined) {
      return {
        ...(failed.construct !== undefined
          ? { construct: failed.construct }
          : {}),
        reason: `'${displayName(ref)}' could not be modeled: ${failed.reason}`,
      };
    }
  }
  // A keyword union normalizes to its deduplicated tags; a member outside
  // the keywords refuses at that member, not at the union.
  if (ts.isUnionTypeNode(t) && reg.unions) {
    const tags = keywordTags(t);
    if (!Array.isArray(tags)) return constructAt(tags, tags.kind, sf);
    return normalizedUnion(tags, t, sf);
  }
  return constructAt(t, t.kind, sf);
}

/** The tags a type node denotes — one for a bare keyword, several for a
 * union of them — or the member that falls outside the keyword domain,
 * which is where a union refuses rather than at the union itself. */
function keywordTags(t: ts.TypeNode): UnionTag[] | ts.TypeNode {
  if (!ts.isUnionTypeNode(t)) {
    const tag = keywordTag(t);
    return tag === undefined ? t : [tag];
  }
  const tags: UnionTag[] = [];
  for (const m of t.types) {
    const tag = keywordTag(m);
    if (tag === undefined) return m;
    tags.push(tag);
  }
  return tags;
}

/** Tags deduplicated into normalization order. A one-tag union is its
 * base type, and only `number` has a model as one. */
function normalizedUnion(
  tags: UnionTag[],
  t: ts.TypeNode,
  sf: ts.SourceFile,
): ValueTy | FailedDecl {
  const union = UNION_TAGS.filter((tag) => tags.includes(tag));
  if (union.length >= 2) return { union: [...union] };
  if (union[0] === "number") return "num";
  return constructAt(t, t.kind, sf);
}

/** A walked parameter list: names with their types and whether a call
 * may omit them, in declaration order. */
type WalkedParams = { name: string; ty: ValueTy; optional: boolean }[];

/** Names and types for a parameter list, or the first failure — the
 * shape check ahead of the type, as the old order has it. */
function walkParams(
  params: readonly ts.ParameterDeclaration[],
  sf: ts.SourceFile,
  reg: ParamReg,
  shapeFailure: (
    p: ts.ParameterDeclaration,
    sf: ts.SourceFile,
  ) => FailedDecl | undefined,
): WalkedParams | FailedDecl {
  const out: WalkedParams = [];
  let seenOptional = false;
  for (const p of params) {
    const failure = shapeFailure(p, sf);
    if (failure !== undefined) return failure;
    const optional = p.questionToken !== undefined;
    // Optionals must be trailing, or an omitted argument would have no
    // one position to land in. TypeScript says so too, but a run without
    // a tsconfig never type-checks, so the walk re-checks rather than
    // trusting tsc to have refused the file.
    if (seenOptional && !optional) return constructAt(p, p.kind, sf);
    seenOptional ||= optional;
    const ty = paramValueTy(p, sf, reg);
    if (typeof ty !== "string" && "reason" in ty) return ty;
    out.push({ name: (p.name as ts.Identifier).text, ty, optional });
  }
  return out;
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
    /* v8 ignore next 2 -- every class-element kind is handled or
       returned above; the fallthrough guards against new ones. */
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
  // The class is not in the registries while its own constructor walks,
  // so a parameter typed at it refuses — the direct cycle has no model.
  const ctorReg: ParamReg = {
    classes: c.classes,
    failed: c.failed,
    names,
    module: qualifier,
    unions: false,
  };
  const ctorParams = walkParams(ctor.parameters, sf, ctorReg, ctorParamFailure);
  if (!Array.isArray(ctorParams)) return ctorParams;
  const base = {
    mapped: c.mapped,
    failed: c.failed,
    classes: c.classes,
    constants: c.constants,
    aliases: c.aliases,
    names,
    module: qualifier,
  };
  const ctorScope: WalkScope = {
    ...base,
    vars: new Map(ctorParams.map((p) => [p.name, p.ty])),
  };
  const fieldSet = new Set(fields);
  const ctorLocals: Locals = new Map(
    ctorParams.map((p) => [p.name, "mutable" as const]),
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
    ctorBody = lowerTree(
      tree,
      ctorParams.map((p) => [p.name, p.ty] as const),
      () => {},
      ctorScope,
      sf,
    );
  } catch (err) {
    if (err instanceof CtorPrecondition)
      return { construct: "constructor", reason: err.message };
    /* v8 ignore next -- the walk throws nothing else */
    if (!(err instanceof ModelError)) throw err;
    return modelFailure(err);
  }

  // `ctorReg` bans unions, so this restates the ban where the shape is
  // recorded rather than trusting the flag everywhere downstream.
  const shapeCtorParams: CtorValueTy[] = [];
  for (const p of ctorParams) {
    /* v8 ignore next 2 -- unreachable: ctorReg refused the union first. */
    if (typeof p.ty !== "string" && "union" in p.ty)
      return constructAt(ctor, ctor.kind, sf);
    shapeCtorParams.push(p.ty);
  }

  const methodSigs = new Map<string, FnSig>();
  const shape: ClassShape = {
    fields,
    getters: getterNames,
    ctorParams: shapeCtorParams,
    ctorParamNames: ctorParams.map((p) => p.name),
    methods: methodSigs,
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
    const scope: WalkScope = {
      ...base,
      vars: new Map(),
      self,
      selfFailed: memberFailed,
    };
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
      memberFailed.set(memberKey(spelling), modelFailure(err));
    }
  }
  // Getters render ahead of methods, so a getter body sees an empty
  // method map: a getter calling a method degrades alone. A method reads
  // members off an instance of its own class, so its receiver shape
  // carries the getters that actually modeled, not the declared ones.
  const methodSelf = {
    ref: self.ref,
    shape: { ...shape, getters: new Set(getters.map((g) => g.name)) },
  };
  const methodReg: ParamReg = { ...ctorReg, unions: true, self: self.ref };
  const methods: EmitMethod[] = [];
  for (const m of methodDecls) {
    const spelling = (m.name as ts.Identifier | ts.PrivateIdentifier).text;
    const walked = methodFailure(m, className, spelling, sf, methodReg);
    if (!("params" in walked)) {
      memberFailed.set(memberKey(spelling), walked);
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
    const params = walked.params;
    const scope: WalkScope = {
      ...base,
      vars: new Map(params.map((p) => [p.name, p.ty])),
      self: methodSelf,
      selfFailed: memberFailed,
    };
    const locals: Locals = new Map(
      params.map((p) => [p.name, "mutable" as const]),
    );
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
        params: params.map((p) => wireParam(p.name, p.ty)),
        body: lowerTree(
          body,
          params.map((p) => [p.name, p.ty] as const),
          () => {
            throw new ModelError("the body must return on every path");
          },
          scope,
          sf,
        ),
      });
      methodSigs.set(spelling, sigOf(params));
    } catch (err) {
      /* v8 ignore next -- the walk throws nothing else */
      if (!(err instanceof ModelError)) throw err;
      memberFailed.set(memberKey(spelling), modelFailure(err));
    }
  }
  return {
    emit: {
      kind: "class",
      name: className,
      ...(qualifier !== "" ? { module: qualifier } : {}),
      source: cls.getText(sf),
      fields,
      ctor: {
        params: ctorParams.map((p) => wireParam(p.name, p.ty)),
        body: ctorBody,
      },
      getters,
      methods,
    },
    shape: {
      ...shape,
      getters: new Set(getters.map((g) => g.name)),
      methods: methodSigs,
    },
    memberFailed,
  };
}

/** A method outside the slice degrades alone: privacy, asynchrony, a
 * signature the model cannot read, or a name the model reserves. Its
 * walked parameters come back with it. */
function methodFailure(
  m: ts.MethodDeclaration,
  className: string,
  spelling: string,
  sf: ts.SourceFile,
  reg: ParamReg,
): { params: WalkedParams } | FailedDecl {
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
  const params = walkParams(m.parameters, sf, reg, methodParamFailure);
  if (!Array.isArray(params)) return params;
  if (m.type === undefined) return constructAt(m, m.kind, sf);
  if (m.type.kind !== ts.SyntaxKind.NumberKeyword)
    return constructAt(m.type, m.type.kind, sf);
  return { params };
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
): { emit: EmitFunction; sig: FnSig } | FailedDecl {
  const sig = signatureFailure(fn, sf, {
    classes: c.classes,
    failed: c.failed,
    names,
    module,
    unions: true,
  });
  if (!("params" in sig)) return sig;
  const params = sig.params;
  const scope: WalkScope = {
    vars: new Map(params.map((p) => [p.name, p.ty])),
    mapped: c.mapped,
    failed: c.failed,
    classes: c.classes,
    constants: c.constants,
    aliases: c.aliases,
    names,
    module,
  };
  // Parameters are assignable, the way JavaScript has them.
  const locals: Locals = new Map(
    params.map((p) => [p.name, "mutable" as const]),
  );
  const tree = fn.body!.statements.flatMap((s) =>
    structureStmt(s, sf, locals, scope),
  );
  const prescan = bodyPrescan(tree, sf, scope);
  if (prescan !== undefined) return prescan;
  try {
    const body = lowerTree(
      tree,
      params.map((p) => [p.name, p.ty] as const),
      () => {
        // A `number` function that runs off the end returns undefined,
        // which this slice has no value for.
        throw new ModelError("the body must return on every path");
      },
      scope,
      sf,
    );
    return {
      emit: {
        kind: "function",
        name: fn.name!.text,
        ...(module !== "" ? { module } : {}),
        params: params.map((p) => wireParam(p.name, p.ty)),
        source: fn.getText(sf),
        body,
      },
      sig: sigOf(params),
    };
  } catch (err) {
    if (err instanceof ModelError) return modelFailure(err);
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

/** A whitelisted builtin as a use site needs it: the source spelling
 * (for messages), the IR kind, and the value type it yields. */
interface BuiltinEntry {
  name: string;
  kind: BuiltinKind;
  ty: Expected;
}

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
): (BuiltinEntry & { arg: ts.Expression }) | undefined {
  if (!ts.isCallExpression(e) || e.arguments.length !== 1) return undefined;
  const callee = e.expression;
  // A call through a module-level alias of a builtin lowers as the
  // builtin itself; a local binding of the spelling shadows the alias.
  if (ts.isIdentifier(callee) && !scope.vars.has(callee.text)) {
    const alias = scope.aliases.get(modelKey(refOf(scope, callee.text)));
    if (alias !== undefined) return { ...alias, arg: e.arguments[0]! };
  }
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

/** A class binder's IR, or the refusal it earns. The binder ranges over
 * the image of successful construction, so the class and every one of its
 * constructor parameters have to be inside the model; nothing about the
 * clamp or range machinery applies, since the domain is an image. */
function lowerClassBinder(
  name: string,
  className: string,
  classes: ReadonlyMap<string, ClassShape>,
  failed: ReadonlyMap<string, FailedDecl>,
  names: ReadonlyMap<string, ModelRef>,
  module: string,
): EmitBinder | { reason: string } {
  const ref = names.get(className) ?? { module, name: className };
  const shape = classes.get(modelKey(ref));
  if (shape === undefined) {
    const why =
      failed.get(modelKey(ref))?.reason ??
      `no model registered for '${displayName(ref)}'`;
    return {
      reason:
        `class-valued binder '${className}' names a class outside ` +
        `the model: ${why}`,
    };
  }
  return {
    name,
    kind: "class",
    className,
    ...(ref.module !== "" ? { module: ref.module } : {}),
    ctorParams: lowerCtorParams(shape, classes),
  };
}

/** A class's constructor parameters as the wire carries them. A class walks
 * only after every class its parameters name, so the lookup always hits and
 * the recursion always bottoms out. */
function lowerCtorParams(
  shape: ClassShape,
  classes: ReadonlyMap<string, ClassShape>,
): EmitCtorParam[] {
  return shape.ctorParams.map((ty, i) => {
    const name = shape.ctorParamNames[i]!;
    if (ty === "num") return { name, kind: "number" };
    const ref = ty.instance;
    const inner = classes.get(modelKey(ref))!;
    return {
      name,
      kind: "class",
      className: ref.name,
      ...(ref.module !== "" ? { module: ref.module } : {}),
      ctorParams: lowerCtorParams(inner, classes),
    };
  });
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
  mapped: ReadonlyMap<string, FnSig>,
  failed: ReadonlyMap<string, FailedDecl>,
  classes: ReadonlyMap<string, ClassShape>,
  constants: ReadonlySet<string>,
  aliases: ReadonlyMap<string, BuiltinEntry>,
  names: ReadonlyMap<string, ModelRef>,
  module: string,
): PayloadResult {
  const bare: PayloadResult = { kind: "payload", payload: { kind: "bare" } };
  try {
    const { binders, body } = parsePrefix(formula);
    const loweredBinders: EmitBinder[] = [];
    const clamped: string[] = [];
    for (const b of binders) {
      if (isClassDomain(b.domain)) {
        const cls = lowerClassBinder(
          b.varName,
          b.domain.className,
          classes,
          failed,
          names,
          module,
        );
        if ("reason" in cls) {
          return {
            kind: "classified",
            szs: "Inappropriate",
            reason: cls.reason,
          };
        }
        loweredBinders.push(cls);
        continue;
      }
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
      // A class binder enters the walk as an instance of its class, so
      // its fields, getters, and methods resolve the way a class-typed
      // parameter's do; every other binder is a number.
      vars: new Map(
        loweredBinders.map((b): [string, ValueTy] => [
          b.name,
          b.kind === "class"
            ? { instance: { module: b.module ?? module, name: b.className } }
            : "num",
        ]),
      ),
      mapped,
      failed,
      classes,
      constants,
      aliases,
      names,
      module,
    };
    // A SameValue conclusion over number operands splits into the JsM
    // equation; one with an operand the tagged domain carries — boolean,
    // undefined, null — is instead a boolean island over JsVal, the same
    // lowering the atom gets in a guard or a branch condition.
    const asEquation =
      sides !== undefined && !sides.some((s) => taggedOperand(s, scope));
    // Guards precede the conclusion in the old elaborator's tree order, so
    // the first refusal either pipeline reports is the same one. The
    // conclusion is pre-scanned as written — an equation splits into its
    // sides only for the typed walk, which lifts them separately.
    const prescanRoots: ScanRoot[] = [...guardRoots, { expr, sf: parsed.sf }];
    const walkRoots: (ScanRoot & { expected: Expected })[] = [
      ...guardRoots,
      ...(asEquation
        ? [
            { expr: sides![0]!, sf: parsed.sf, expected: "num" as Expected },
            { expr: sides![1]!, sf: parsed.sf, expected: "num" as Expected },
          ]
        : [{ expr, sf: parsed.sf, expected: "bool" as Expected }]),
    ];
    // A property the model refuses is `Inappropriate`; one the typed walk
    // fails is a failed property elaboration, the engine's `Error`.
    const found = prescanFailure(prescanRoots, scope);
    if (found !== undefined) {
      return { kind: "classified", szs: "Inappropriate", reason: found.reason };
    }
    const walkedRoots: EmitExpr[] = [];
    for (const root of walkRoots) {
      const walked = typedOrFailure(root.expr, root.expected, scope, root.sf);
      if (!("expr" in walked)) {
        // A failure that traveled from a degraded declaration is the
        // input's refusal; only the engine's own gaps are its `Error`.
        if (walked.construct !== undefined) {
          return {
            kind: "classified",
            szs: "Inappropriate",
            reason: walked.reason,
          };
        }
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
        conclusion: asEquation
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
    // An unreadable formula is the input's fault, never a verdict; the
    // CLI rejects it before emission, so a reject reaching here must
    // travel, not degrade.
    if (e instanceof LemmaError) throw e;
    return bare;
  }
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
  mapped: Map<string, FnSig>;
  failed: Map<string, FailedDecl>;
  classes: Map<string, ClassShape>;
  constants: Set<string>;
  aliases: Map<string, BuiltinEntry>;
}

/** The literal a module-scope declarator pins, when the model admits it:
 * a `const` with an identifier name, a numeric-literal initializer (unary
 * minus included), and no type annotation other than `number`. */
function constantLiteral(d: ts.VariableDeclaration): string | undefined {
  if (!ts.isIdentifier(d.name)) return undefined;
  if (d.type !== undefined && d.type.kind !== ts.SyntaxKind.NumberKeyword)
    return undefined;
  /* v8 ignore next -- an uninitialized `const` does not typecheck, and the
     run is gated on the project typechecking; `declare` is not admissible. */
  if (d.initializer === undefined) return undefined;
  const init = unwrapParens(d.initializer);
  if (ts.isNumericLiteral(init)) return numberToken(init);
  const negated = negatedLiteral(init);
  if (negated !== undefined) return `-${numberToken(negated)}`;
  return undefined;
}

/** The whitelisted builtin a module-scope declarator aliases, when the
 * model admits it: a `const` with an identifier name, no type annotation,
 * and exactly a whitelisted member spelling as initializer — declined
 * when the module itself binds the namespace spelling, since the
 * initializer then reads that binding, not the standard library. */
function builtinAlias(
  d: ts.VariableDeclaration,
  binds: (name: string) => boolean,
): BuiltinEntry | undefined {
  if (!ts.isIdentifier(d.name) || d.type !== undefined) return undefined;
  /* v8 ignore next -- as in `constantLiteral`: the declarator reaching here
     is a `const` a typechecked project admits, so it has an initializer. */
  if (d.initializer === undefined) return undefined;
  const init = unwrapParens(d.initializer);
  if (!ts.isPropertyAccessExpression(init) || !ts.isIdentifier(init.expression))
    return undefined;
  const namespace = init.expression.text;
  if (binds(namespace)) return undefined;
  const name = `${namespace}.${init.name.text}`;
  const entry = BUILTIN_MEMBER_CALLS.get(name);
  if (entry === undefined) return undefined;
  return { name, ...entry };
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
      if ("emit" in walked) {
        c.declarations.push(walked.emit);
        c.mapped.set(key(stmt.name.text), walked.sig);
      } else {
        c.failed.set(key(stmt.name.text), walked);
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
          exactSig(walked.shape.ctorParams),
        );
        for (const g of walked.shape.getters) {
          c.mapped.set(key(qualifiedName(g, className)), exactSig([]));
        }
        for (const [m, sig] of walked.shape.methods) {
          c.mapped.set(key(qualifiedName(m, className)), sig);
        }
        for (const [k, v] of walked.memberFailed) c.failed.set(k, v);
        continue;
      }
      // A class-level failure is every member's failure: the model has no
      // structure to hang a surviving member on.
      c.failed.set(key(className), walked);
      for (const member of stmt.members) {
        const name = member.name;
        // A constructor has no name node; its spelling is synthesized, as
        // the modeling path synthesizes it when registering the ctor.
        const spelling = ts.isConstructorDeclaration(member)
          ? "constructor"
          : name !== undefined && ts.isIdentifier(name)
            ? name.text
            : undefined;
        if (spelling === undefined) continue;
        const isStatic = (
          ts.getModifiers(member as ts.HasModifiers) ?? []
        ).some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
        c.failed.set(key(qualifiedName(spelling, className, isStatic)), walked);
      }
      continue;
    }
    // Every other name a declaration binds degrades to the old pipeline's
    // opaque failure, position on the binding identifier — except a
    // declarator the constant scan positively admits.
    if (ts.isVariableStatement(stmt)) {
      const admissible =
        (stmt.declarationList.flags & ts.NodeFlags.Const) !== 0 &&
        (ts.getModifiers(stmt) ?? []).every(
          (m) => m.kind === ts.SyntaxKind.ExportKeyword,
        );
      const binds = (name: string) =>
        names.has(name) || c.failed.has(key(name));
      for (const d of stmt.declarationList.declarations) {
        const lit = admissible ? constantLiteral(d) : undefined;
        if (lit !== undefined) {
          const name = (d.name as ts.Identifier).text;
          c.declarations.push({
            kind: "constant",
            name,
            ...(qualifier !== "" ? { module: qualifier } : {}),
            lit,
            source: stmt.getText(sf),
          });
          c.constants.add(key(name));
          continue;
        }
        const alias = admissible ? builtinAlias(d, binds) : undefined;
        if (alias !== undefined) {
          c.aliases.set(key((d.name as ts.Identifier).text), alias);
          continue;
        }
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
    constants: new Set(),
    aliases: new Map(),
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
      closure.constants,
      closure.aliases,
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
