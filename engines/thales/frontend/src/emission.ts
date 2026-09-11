import * as path from "node:path";
import ts from "typescript";
import {
  annotationKey,
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
  | { kind: "bool"; value: boolean }
  | { kind: "id"; name: string }
  | { kind: "unop"; op: "-" | "+" | "!"; operand: EmitExpr }
  | { kind: "binop"; op: string; left: EmitExpr; right: EmitExpr }
  | { kind: "same-value"; left: EmitExpr; right: EmitExpr }
  | { kind: "cond"; cond: EmitExpr; then: EmitExpr; else: EmitExpr }
  | { kind: "builtin"; object: string; member: string; args: EmitExpr[] }
  /** A whitelisted standard-library member read: one of the Number
   * constants ECMA-262 fixes. A value, never a callee, so no arguments. */
  | { kind: "builtin-read"; object: string; member: string }
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
  /** A union-typed read at a number or boolean position: the model
   * refuses coercion, so a wrong-tag value throws rather than converting. */
  | { kind: "project"; tag: "number" | "boolean"; expr: EmitExpr }
  /** Injection into an option slot: `some expr` with the operand, `none`
   * without it. */
  | { kind: "option"; expr?: EmitExpr }
  | { kind: "option-test"; expr: EmitExpr; present: boolean }
  /** The throwing projection out of an option slot, the twin of
   * `project`; unreachable behind its test, present so the rendering is
   * total. */
  | { kind: "option-get"; expr: EmitExpr }
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
    }
  /** An unmodelable site inside its owner: the opaque the artifact
   * declares for it, applied to the variables in scope there. */
  | {
      kind: "residual";
      owner: string;
      module?: string;
      site: number;
      args: EmitExpr[];
    };

/** A statement in the shapes the plain-Lean emitter renders as Lean
 * do-notation: `const` and mutable `let` locals, reassignment, `if`/`else`
 * (arms may return, throw, or fall through), `throw`, and `return`. A
 * `throw` carries the error's constructor name alone — the message is a
 * string the value model has nothing to say about. */
export type EmitStmt =
  | { kind: "return"; expr: EmitExpr }
  | { kind: "throw"; error: string }
  /** A local's `type` is present exactly for a boolean, union, or class
   * binding — `"boolean"`, or the same normalized tag array or class
   * reference a parameter's type carries; absent means the numeric slice
   * the statement always had. */
  | {
      kind: "const";
      name: string;
      init: EmitExpr;
      type?: UnionTag[] | { class: string; module?: string } | "boolean";
    }
  | {
      kind: "let";
      name: string;
      init: EmitExpr;
      type?: UnionTag[] | { class: string; module?: string } | "boolean";
    }
  | { kind: "assign"; name: string; expr: EmitExpr }
  | { kind: "if"; cond: EmitExpr; then: EmitStmt[]; else?: EmitStmt[] }
  | { kind: "field-set"; field: string; expr: EmitExpr }
  /** An expression statement: evaluated for its effect, value dropped. */
  | { kind: "discard"; expr: EmitExpr };

/** A parameter on the wire: its name and its declared type — a
 * TypeScript number, a boolean, a keyword union's normalized tags, or an
 * instance of a modeled class. */
export interface EmitParam {
  name: string;
  type:
    | "boolean"
    | "number"
    | UnionTag[]
    | { class: string; module?: string }
    | { option: { class: string; module?: string } };
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
  /** Present exactly for a boolean-returning declaration; absent means
   * the number every declaration returned before. */
  returns?: "boolean";
  /** Present exactly when the body reaches a residual site, directly or
   * through a callee that does. A valueless opaque compiles to `pure`, so
   * without this the evaluation rung would prove straight through one. */
  noncomputable?: true;
}

export interface EmitGetter {
  name: string;
  body: EmitStmt[];
  /** Present exactly for a boolean-returning declaration; absent means
   * the number every declaration returned before. */
  returns?: "boolean";
  noncomputable?: true;
}

export interface EmitMethod {
  name: string;
  params: EmitParam[];
  body: EmitStmt[];
  /** Present exactly for a boolean-returning declaration; absent means
   * the number every declaration returned before. */
  returns?: "boolean";
  noncomputable?: true;
}

/** A field on the wire: its spelling and, for a boolean, union, or class
 * field, its type — absent means number, the rule a local statement follows. */
export interface EmitField {
  name: string;
  type?: UnionTag[] | { class: string; module?: string } | "boolean";
}

/** A class as the emitter renders it: a structure over its fields, a
 * constructor that assigns each exactly once, and one function per
 * modeled getter or method. */
export interface EmitClass {
  kind: "class";
  name: string;
  /** The defining module's entry-relative path; absent for the entry. */
  module?: string;
  /** Fields in declaration order; a private one keeps its '#'. */
  fields: EmitField[];
  source: string;
  ctor: { params: EmitParam[]; body: EmitStmt[]; noncomputable?: true };
  getters: EmitGetter[];
  methods: EmitMethod[];
}

/** A module-level `const` whose initializer is a constant expression: a
 * named value the model admits, read wherever a number is expected.
 * Soundness needs two immutabilities at once: `const` pins the binding (a
 * `let` or `var` is reassignable from any function, so its reads have no
 * one value to model), and the numeric value pins itself — a primitive
 * has no mutable state, so no code can change what a read denotes. A
 * `const` over an object value would satisfy only the first, which is
 * why object initializers stay degraded. */
export interface EmitConstant {
  kind: "constant";
  name: string;
  /** The defining module's entry-relative path; absent for the entry. */
  module?: string;
  /** The initializer as written — literals, reads of constants admitted
   * above it, arithmetic and unary sign — so the def preserves the
   * source's derivation rather than a value the reader must re-derive. */
  init: EmitExpr;
  source: string;
}

/** One residual site: the opaque its owner declares — one component below
 * the owner's model name, numbered from 1 in source order within that
 * owner — over the modeled variables in scope where the site arose, with
 * the refusal text that names the construct as its docstring. Emitted
 * ahead of its owner, so the artifact declares a site before using it. */
export interface EmitResidualDecl {
  kind: "residual";
  /** The qualified name of the callable that owns the site: `f`, or
   * `C#member` with `constructor` for a constructor's own. */
  owner: string;
  /** The defining module's entry-relative path; absent for the entry. */
  module?: string;
  site: number;
  /** The refusal's reason text, which names the construct. */
  construct: string;
  /** The receiver first inside a member, then the variables in scope. */
  params: EmitParam[];
  /** The codomain; the renderer wraps it in `JsM`, since unmodeled code
   * may throw. */
  type: EmitParam["type"];
}

export type EmitDecl =
  EmitFunction | EmitClass | EmitConstant | EmitResidualDecl;

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

/** A value's type in the walk: a number, a boolean, a keyword union, or
 * an instance of a modeled class. Parameters and fields carry number,
 * union, and instance; locals carry all four; returns are numbers. */
export type ValueTy =
  | "num"
  | "bool"
  | { instance: ModelRef }
  | { union: UnionTag[] }
  /** A defaulted class parameter's slot: the instance or `undefined`,
   * which the tagged domain cannot hold, so it is Lean's `Option`. */
  | { option: ModelRef };

function isOptionTy(t: Expected): t is { option: ModelRef } {
  return typeof t !== "string" && "option" in t;
}

/** Whether two model references name the same class. */
function sameClass(a: ModelRef, b: ModelRef): boolean {
  return a.module === b.module && a.name === b.name;
}

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
  if (ty === "bool") return { name, type: "boolean" };
  if ("union" in ty) return { name, type: [...ty.union] };
  if ("option" in ty) {
    const { module, name: cls } = ty.option;
    return {
      name,
      type: { option: { class: cls, ...(module !== "" ? { module } : {}) } },
    };
  }
  const { module, name: cls } = ty.instance;
  return {
    name,
    type: { class: cls, ...(module !== "" ? { module } : {}) },
  };
}

/** What a function, method, or getter returns: the number every callable
 * returned before, or a boolean. */
export type ReturnTy = "num" | "bool";

/** A callable's signature: its slot types in declaration order, the
 * fewest arguments a call may supply — one past the last parameter that
 * is neither optional nor defaulted, everything up to `params.length`
 * filling at the call — and its declared return type. */
export interface FnSig {
  params: ValueTy[];
  minArgs: number;
  returns: ReturnTy;
}

function sigOf(params: WalkedParams, returns: ReturnTy): FnSig {
  return {
    params: params.map((p) => p.slot),
    minArgs:
      params.map((p) => p.optional || p.init !== undefined).lastIndexOf(false) +
      1,
    returns,
  };
}

/** A fixed-arity signature: what a getter has. */
function exactSig(params: ValueTy[], returns: ReturnTy = "num"): FnSig {
  return { params, minArgs: params.length, returns };
}

/** The arity check every call shares. A call may omit arguments the
 * signature fills — trailing optionals and defaults — and nothing else;
 * tsc refuses the rest first, in bodies through the gate and in atoms
 * through island typing, so a miss here is an invariant. */
function checkArity(name: string, sig: FnSig, got: number): void {
  const total = sig.params.length;
  if (got >= sig.minArgs && got <= total) return;
  const expected =
    sig.minArgs === total ? `${total}` : `${sig.minArgs} to ${total}`;
  throw new ModelError(`'${name}' expects ${expected} argument(s), got ${got}`);
}

/** A construction's arity: the same rule a call has. */
function checkCtorArity(ref: ModelRef, shape: ClassShape, got: number): void {
  const total = shape.ctorParams.length;
  if (got >= shape.ctorRequired && got <= total) return;
  const expected =
    shape.ctorRequired === total
      ? `${total}`
      : `${shape.ctorRequired} to ${total}`;
  throw new ModelError(
    `'${displayName(ref)}' expects ${expected} argument(s), got ${got}`,
  );
}

/** What an omitted argument becomes at a slot that admits omission. */
function fillOmitted(slot: ValueTy): EmitExpr {
  return isOptionTy(slot)
    ? { kind: "option" }
    : { kind: "inject", tag: "undefined" };
}

/** A call's arguments against a signature, each omitted trailing one
 * filled with the `undefined` that parameter's own union carries. */
function walkArgs(
  args: readonly ts.Expression[],
  sig: FnSig,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr[] {
  return sig.params.map((ty, i): EmitExpr => {
    const a = args[i];
    return a === undefined ? fillOmitted(ty) : walkTyped(a, ty, scope, sf);
  });
}

/** A construction's arguments against the class's slots, each omitted
 * trailing one filled with the slot's own `undefined`. */
function walkCtorArgs(
  args: readonly ts.Expression[],
  shape: ClassShape,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr[] {
  return shape.ctorParams.map((slot, i): EmitExpr => {
    const a = args[i];
    return a === undefined ? fillOmitted(slot) : walkTyped(a, slot, scope, sf);
  });
}

/** What a use of a class needs to know: its fields in declaration order,
 * the getters that modeled, and its constructor's signature. */
export interface ClassShape {
  /** The fields in declaration order with their declared types. */
  fields: ReadonlyMap<string, ValueTy>;
  /** The getters that modeled, each with its declared return type. */
  getters: ReadonlyMap<string, ReturnTy>;
  /** The slot types a construction fills, in declaration order: a number,
   * a boolean, an instance, or — for a defaulted parameter — its boundary
   * union. */
  ctorParams: ValueTy[];
  /** The constructor parameters' source spellings, positionally aligned
   * with `ctorParams`. A class binder quantifies over them by name. */
  ctorParamNames: string[];
  /** Leading parameters a construction must supply: one past the last
   * without a default. Everything past it fills at the call. */
  ctorRequired: number;
  /** Modeled methods by name, with their signatures. */
  methods: ReadonlyMap<string, FnSig>;
}

/** A binder's denoted domain: a finite half-open integer range, the whole
 * int line, the naturals, the two booleans, or a `number` binder — the
 * whole double line, narrowed by whichever bounds its interval carries.
 * These are the shapes `ThalesEmit/Render.lean` renders as ∀ heads. */
export type EmitBinder =
  | { name: string; kind: "range"; lo: string; hi: string }
  | { name: string; kind: "int" }
  | { name: string; kind: "nat" }
  | { name: string; kind: "boolean" }
  | { name: string; kind: "number"; lower?: FloatBound; upper?: FloatBound }
  | {
      name: string;
      kind: "class";
      className: string;
      module?: string;
      ctorParams: EmitCtorParam[];
    };

/** One constructor parameter of a class binder's class. A class-typed one
 * carries its own parameters, so the tree bottoms out in numbers and
 * booleans. A defaulted one is quantified at its declared type and
 * injected into its boundary slot at the construct call. */
export type EmitCtorParam =
  | { name: string; kind: "number"; defaulted?: true }
  | { name: string; kind: "boolean"; defaulted?: true }
  | {
      name: string;
      kind: "class";
      className: string;
      module?: string;
      ctorParams: EmitCtorParam[];
      defaulted?: true;
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
 * (`Inappropriate`) or failed by the engine's own gaps (`Error`), with the
 * reason the CLI reports verbatim — `tests/fixtures/envelopes.expected.json`
 * pins it. */
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

/** Why a declaration is not in the model. A construct name is present
 * exactly when the failure is a statement about the input rather than about
 * the engine — which is what separates Inappropriate from Error. */
interface FailedDecl {
  construct?: string;
  reason: string;
}

/** The global number constants the walk models — exact binary64 values,
 * the fallback JavaScript makes them, never keywords. */
const GLOBAL_NUMBER_ATOMS = new Set(["NaN", "Infinity"]);

const ARITH_OPERATORS = new Set(["+", "-", "*", "/", "%"]);
const COMPARISON_OPERATORS = new Set(["<", "<=", ">", ">=", "===", "!=="]);
const LOGICAL_OPERATORS = new Set(["||", "&&"]);

const modeledOperator = (op: string): boolean =>
  ARITH_OPERATORS.has(op) ||
  COMPARISON_OPERATORS.has(op) ||
  LOGICAL_OPERATORS.has(op);

/** A binary operator outside the model, named the way an unlisted builtin
 * member is: the source wrote real JavaScript this implementation does
 * not take yet, which is all the reason can honestly say. */
function unsupportedOperator(op: string): FailedDecl {
  return { construct: op, reason: `'${op}' is not supported` };
}

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

/** `true`/`false`: reserved words, so no binding can shadow them. */
function booleanLiteral(e: ts.Expression): boolean | undefined {
  if (e.kind === ts.SyntaxKind.TrueKeyword) return true;
  if (e.kind === ts.SyntaxKind.FalseKeyword) return false;
  return undefined;
}

/** Whether a member chain's root is one the typed walk will type: `this`
 * inside a member, a class-typed identifier, or a construction — one of
 * an unregistered or degraded name included, so that failure travels to
 * the walk rather than being reported as a shape. */
function receiverShaped(e: ts.Expression, scope: WalkScope): boolean {
  const u = unwrapParens(e);
  if (u.kind === ts.SyntaxKind.ThisKeyword) return scope.self !== undefined;
  if (ts.isIdentifier(u)) {
    const ty = scope.vars.get(u.text);
    return ty !== undefined && typeof ty !== "string" && "instance" in ty;
  }
  if (newCall(u) !== undefined) return true;
  const inner = memberAccess(u);
  return inner !== undefined && receiverShaped(inner.receiver, scope);
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
  // A whitelisted builtin is a member call too, and answers first: its
  // receiver is a namespace, not an instance place.
  const builtin = builtinCall(u, scope);
  if (builtin !== undefined) return builtin.ty === "num";
  if (builtinRead(u, scope) !== undefined) return true;
  const member = memberCall(u) ?? memberAccess(u);
  if (member !== undefined)
    return (
      receiverShaped(member.receiver, scope) && callReturns(u, scope) !== "bool"
    );
  return (
    ts.isCallExpression(u) &&
    ts.isIdentifier(u.expression) &&
    callReturns(u, scope) !== "bool"
  );
}

/** What a call to a modeled callee — a free function, a method on an
 * instance place, or a getter read on one — is declared to return;
 * undefined for anything else, whose own refusal the walk reports. */
function callReturns(u: ts.Expression, scope: WalkScope): ReturnTy | undefined {
  if (ts.isCallExpression(u) && ts.isIdentifier(u.expression)) {
    if (scope.vars.has(u.expression.text)) return undefined;
    return scope.mapped.get(modelKey(refOf(scope, u.expression.text)))?.returns;
  }
  if (
    builtinCall(u, scope) !== undefined ||
    builtinRead(u, scope) !== undefined
  )
    return undefined;
  const call = memberCall(u);
  const member = call ?? memberAccess(u);
  if (member === undefined) return undefined;
  const recv = receiverTy(member.receiver, scope);
  if (recv === undefined || typeof recv === "string" || !("instance" in recv))
    return undefined;
  const shape = classView(scope, recv.instance)?.shape;
  /* v8 ignore next -- classView returns undefined only for the ref classView
     itself already marks unreachable: an instance place always names an
     already-modeled class or the enclosing one. */
  if (shape === undefined) return undefined;
  return call !== undefined
    ? shape.methods.get(call.name)?.returns
    : shape.getters.get(member.name);
}

/** Whether an expression's own shape can denote a boolean in this slice:
 * a literal, a name bound at boolean, a comparison, a SameValue call, a
 * logical combination of them, or a call to a boolean-returning callee.
 * Top-level shape only: deeper offenders keep their own refusals. */
function booleanShaped(e: ts.Expression, scope: WalkScope): boolean {
  const u = unwrapParens(e);
  if (booleanLiteral(u) !== undefined) return true;
  // A union place carrying `boolean` denotes one here, lowering as the
  // throwing projection; it precedes the name and member arms, which type
  // a place at its own union rather than at `bool`.
  if (booleanUnionPlace(u, scope)) return true;
  if (ts.isIdentifier(u)) return scope.vars.get(u.text) === "bool";
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
  if (callReturns(u, scope) === "bool") return true;
  // A boolean field read on an instance place is a boolean, as a bound
  // name is; the place resolver types it off the field's declaration.
  if (memberAccess(u) !== undefined) return placeTy(u, scope) === "bool";
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

/** `typeof v === "lit"` / `!==`, either side order, `v` a place: the one
 * typeof shape the model reads. Shape only — validity (a union-typed
 * operand, a recognized literal) is the walk's question. */
function typeofTest(e: ts.BinaryExpression):
  | {
      typeofNode: ts.TypeOfExpression;
      operand: ts.Expression;
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
    const lit = unwrapParens(b);
    if (!ts.isStringLiteral(lit)) return undefined;
    return { typeofNode: t, operand, result: lit.text };
  };
  const found = pick(e.left, e.right) ?? pick(e.right, e.left);
  return found === undefined ? undefined : { ...found, negated: op === "!==" };
}

/** Whether a recognized typeof-test shape is inside the model: the
 * operand is a union-typed place and the literal is a typeof result. */
function validTypeofTest(
  tt: { operand: ts.Expression; result: string },
  scope: WalkScope,
): boolean {
  return isUnionPlace(tt.operand, scope) && TYPEOF_RESULTS.has(tt.result);
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

/** A member access chain is shaped when its root is: `this` inside a
 * member, an identifier bound at a class, or a construction (whose
 * arguments are scanned). Which members exist is the walk's question,
 * as it always was for `this.x`. An unshaped root is reported at `at`,
 * the whole member expression, which is where the scan always reported
 * a member read or call it could not map. */
function receiverConstruct(
  e: ts.Expression,
  at: ts.Expression,
  sf: ts.SourceFile,
  scope: WalkScope,
): FailedDecl | undefined {
  const u = unwrapParens(e);
  if (u.kind === ts.SyntaxKind.ThisKeyword)
    return scope.self !== undefined ? undefined : constructAt(at, at.kind, sf);
  if (ts.isIdentifier(u)) {
    const ty = scope.vars.get(u.text);
    return ty !== undefined && typeof ty !== "string" && "instance" in ty
      ? undefined
      : constructAt(at, at.kind, sf);
  }
  const built = newCall(u);
  if (built !== undefined) return findConstruct(built, sf, scope);
  const inner = memberAccess(u);
  if (inner !== undefined)
    return receiverConstruct(inner.receiver, at, sf, scope);
  return constructAt(at, at.kind, sf);
}

/** The first construct in tree order this slice cannot map: anything
 * outside identifiers, numeric literals, unary ±,
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
  if (booleanLiteral(e) !== undefined) return undefined;
  if (negatedLiteral(e) !== undefined) return undefined;
  if (isUnaryArith(e)) return findConstruct(e.operand, sf, scope);
  if (ts.isBinaryExpression(e)) {
    const tt = typeofTest(e);
    if (tt !== undefined) {
      if (validTypeofTest(tt, scope)) return undefined;
      return constructAt(tt.typeofNode, tt.typeofNode.kind, sf);
    }
    const op = e.operatorToken.getText();
    if (!modeledOperator(op)) return unsupportedOperator(op);
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
  if (builtin !== undefined) {
    for (const a of builtin.args) {
      const found = findConstruct(a, sf, scope);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  const unsupported = unsupportedBuiltin(e, scope);
  if (unsupported !== undefined) return unsupported;
  // A whitelisted read is a value with no operands to scan.
  if (builtinRead(e, scope) !== undefined) return undefined;
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    for (const a of e.arguments) {
      const found = findConstruct(a, sf, scope);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  const mc = memberCall(e);
  if (mc !== undefined) {
    const found = receiverConstruct(mc.receiver, e, sf, scope);
    if (found !== undefined) return found;
    for (const a of mc.args) {
      const inner = findConstruct(a, sf, scope);
      if (inner !== undefined) return inner;
    }
    return undefined;
  }
  const ma = memberAccess(e);
  if (ma !== undefined) return receiverConstruct(ma.receiver, e, sf, scope);
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
  // A builtin member call has no user callee; its arguments carry them.
  if (builtin !== undefined) {
    for (const a of builtin.args) callNames(a, scope, into);
    return into;
  }
  const mc = memberCall(e);
  if (mc !== undefined) {
    // A member is not a callee of its own; the receiver chain and the
    // arguments carry them.
    callNames(mc.receiver, scope, into);
    for (const a of mc.args) callNames(a, scope, into);
    return into;
  }
  const ma = memberAccess(e);
  if (ma !== undefined) return callNames(ma.receiver, scope, into);
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
  /** Set inside a constructor body: the fields a `this.F = e` may set,
   * each with the type its right side is walked at. */
  ctorFields?: ReadonlyMap<string, ValueTy>;
  /** Set exactly while a body or a default initializer is walked, never on
   * the formula side: where an unmodelable expression becomes a site
   * instead of failing its declaration. */
  residuals?: ResidualSink;
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
 * any other reason is left to the typed walk, which reports it by name. */
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

/** A degraded member's refusal, read off whichever registry the receiver's
 * class resolves against — the live one during that class's own walk. The
 * walk consults this where a member is missing from the shape, so a use of
 * a member that degraded travels that member's own construct instead of
 * reporting the engine broken. */
function memberTravel(
  scope: WalkScope,
  cls: ModelRef,
  member: string,
): FailedDecl | undefined {
  const view = classView(scope, cls);
  if (view === undefined) return undefined;
  return travelFrom(view.failed, {
    module: cls.module,
    name: qualifiedName(member, cls.name),
  });
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
  // A bare `this` names no declaration this function classifies.
  if (e.kind === ts.SyntaxKind.ThisKeyword) return undefined;
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
  if (builtin !== undefined) {
    for (const a of builtin.args) {
      const found = findFailedMemberUse(a, scope);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  const call = memberCall(e);
  const mc = call ?? memberAccess(e);
  if (mc !== undefined) {
    const found = findFailedMemberUse(mc.receiver, scope);
    if (found !== undefined) return found;
    const ty = receiverTy(mc.receiver, scope);
    if (ty !== undefined && typeof ty !== "string" && "instance" in ty) {
      const view = classView(scope, ty.instance);
      // The live registry holds only already-walked siblings, so a
      // forward call still falls to the typed walk, as source order demands.
      if (view !== undefined) {
        const known =
          call !== undefined
            ? view.shape.methods.has(mc.name)
            : view.shape.getters.has(mc.name) || view.shape.fields.has(mc.name);
        if (!known) {
          const travelled = travelFrom(view.failed, {
            module: ty.instance.module,
            name: qualifiedName(mc.name, ty.instance.name),
          });
          if (travelled !== undefined) return travelled;
        }
      }
    }
    for (const a of call?.args ?? []) {
      const inner = findFailedMemberUse(a, scope);
      if (inner !== undefined) return inner;
    }
    return undefined;
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

type Expected = ValueTy;

function describeTy(t: Expected): string {
  if (t === "num") return "a number";
  if (t === "bool") return "a boolean";
  if ("union" in t) return `a '${t.union.join(" | ")}' value`;
  // The walk dispatches an option slot before any mismatch is reported,
  // so no message names one; the arm keeps the description total.
  /* v8 ignore next 2 */
  if ("option" in t)
    return `an optional instance of '${displayName(t.option)}'`;
  return `an instance of '${displayName(t.instance)}'`;
}

/** The typed walk's refusal. Without a construct it is an invariant: the
 * gate guarantees a strict-clean program and the CLI's island typing a
 * tsc-clean formula, so an arity, binding, member, or type mismatch here
 * — in a body or an atom — means the walk's typing disagrees with tsc: an
 * engine fault, reported `Error`. A construct rides along when the failure
 * is the input's (a degraded declaration, an unmodeled operator), keeping
 * the classification `Inappropriate` through every catch that wraps the
 * walk. */
class ModelError extends Error {
  constructor(
    reason: string,
    readonly construct?: string,
  ) {
    super(reason);
  }
}

/** A refusal a residual may not absorb: the site would hide a mutation of
 * the modeled scope. A residual stands for a deterministic, possibly
 * throwing function of the variables in scope; an expression that assigns
 * to one is not that, so it degrades its declaration as before. */
class HardRefusal extends ModelError {}

/** The first assignment, update, or delete anywhere inside an expression. */
function containsMutation(e: ts.Node): ts.Node | undefined {
  if (
    (ts.isBinaryExpression(e) &&
      e.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
      e.operatorToken.kind <= ts.SyntaxKind.LastAssignment) ||
    ((ts.isPrefixUnaryExpression(e) || ts.isPostfixUnaryExpression(e)) &&
      (e.operator === ts.SyntaxKind.PlusPlusToken ||
        e.operator === ts.SyntaxKind.MinusMinusToken)) ||
    ts.isDeleteExpression(e)
  ) {
    return e;
  }
  return ts.forEachChild(e, containsMutation);
}

function mutationRefusal(node: ts.Node, sf: ts.SourceFile): HardRefusal {
  const { line, character } = sf.getLineAndCharacterOfPosition(
    node.getStart(sf),
  );
  return new HardRefusal(
    `an assignment at ${line + 1}:${character + 1} is inside an ` +
      `expression the model cannot follow`,
    "assignment",
  );
}

/** Where a body's residual sites accumulate while it is walked: one sink
 * per callable, shared by every scope derived from that walk, so the
 * numbering is the source order in which the sites arose. */
interface ResidualSink {
  /** The owning callable, as the opaque's name is built from: `f`, or
   * `C#member` with `constructor` for a constructor's own. */
  owner: string;
  /** The owner's module qualifier; empty for the entry. */
  module: string;
  sites: EmitResidualDecl[];
  /** Set inside a member, whose sites take the receiver first. */
  self?: { param: EmitParam; expr: EmitExpr };
  /** Set while a default initializer is walked, which reports its refusals
   * as the parameter's rather than bare. */
  wrap?: (reason: string) => string;
}

/** One unmodelable site: the owner's next opaque, over the variables in
 * scope where it arose, at the type the position expects. */
function residualAt(
  err: ModelError,
  expected: Expected,
  scope: WalkScope,
): EmitExpr {
  const sink = scope.residuals!;
  // Numbered within the owner, though a class's members share one array so
  // the declarations keep the order the members were walked in.
  const site = sink.sites.filter((r) => r.owner === sink.owner).length + 1;
  const vars = [...scope.vars].map(([n, ty]) => wireParam(n, ty));
  const params = sink.self !== undefined ? [sink.self.param, ...vars] : vars;
  const module = sink.module !== "" ? { module: sink.module } : {};
  sink.sites.push({
    kind: "residual",
    owner: sink.owner,
    ...module,
    site,
    construct: sink.wrap !== undefined ? sink.wrap(err.message) : err.message,
    params,
    type: wireParam("_", expected).type,
  });
  const args: EmitExpr[] = vars.map((pa) => ({ kind: "id", name: pa.name }));
  return {
    kind: "residual",
    owner: sink.owner,
    ...module,
    site,
    args: sink.self !== undefined ? [sink.self.expr, ...args] : args,
  };
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
  const travelled = travelFailure(scope, ref);
  if (travelled !== undefined) {
    throw new ModelError(travelled.reason, travelled.construct);
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

/** The typed walk with residuals: a construct-bearing refusal at an
 * expression inside a body becomes that site's opaque instead of failing
 * the declaration. An engine fault, the formula side, and a site that
 * would swallow an assignment still throw. Every recursive call inside
 * `walkStrict` lands here, so the site is the innermost expression that
 * refused and the modeled context above it survives. */
function walkTyped(
  e: ts.Expression,
  expected: Expected,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  try {
    return walkStrict(e, expected, scope, sf);
  } catch (err) {
    if (
      !(err instanceof ModelError) ||
      err instanceof HardRefusal ||
      err.construct === undefined ||
      scope.residuals === undefined
    ) {
      throw err;
    }
    const mutated = containsMutation(e);
    if (mutated !== undefined) throw mutationRefusal(mutated, sf);
    return residualAt(err, expected, scope);
  }
}

/** The typed walk: operand types are checked in tree order, so which
 * failure a declaration reports — and with what message — is fixed by the
 * source rather than by walk order. */
function walkStrict(
  e: ts.Expression,
  expected: Expected,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  if (ts.isParenthesizedExpression(e)) {
    return walkTyped(e.expression, expected, scope, sf);
  }
  if (isUnionTy(expected)) return walkUnionSlot(e, expected.union, scope, sf);
  if (isOptionTy(expected))
    return walkOptionSlot(e, expected.option, scope, sf);
  // A union-typed place at a number position lowers as the throwing
  // projection; the norm layer discharges it on tag-determined paths.
  if (expected === "num" && isUnionPlace(e, scope)) {
    return {
      kind: "project",
      tag: "number",
      expr: resolvePlace(e, scope, sf)!.expr,
    };
  }
  // The boolean twin, gated on the tag: truthiness still has no model, so
  // a union without `boolean` keeps its own refusal.
  if (expected === "bool" && booleanUnionPlace(e, scope)) {
    return {
      kind: "project",
      tag: "boolean",
      expr: resolvePlace(e, scope, sf)!.expr,
    };
  }
  const boolLit = booleanLiteral(e);
  if (boolLit !== undefined) {
    if (expected !== "bool") {
      throw new ModelError(
        `a boolean literal cannot be ${describeTy(expected)}`,
      );
    }
    return { kind: "bool", value: boolLit };
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
    // A union `expected` never reaches here: the slot walk intercepted it,
    // and a union-typed read at `num` projected above.
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
    if (!booleanShaped(e.operand, scope)) {
      const failed = nonBooleanOperand("!", "the operand", e.operand, sf);
      throw new ModelError(failed.reason, failed.construct);
    }
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
    if (!booleanShaped(e.condition, scope)) {
      const failed = nonBooleanOperand("?:", "the condition", e.condition, sf);
      throw new ModelError(failed.reason, failed.construct);
    }
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
        expr: resolvePlace(tt.operand, scope, sf)!.expr,
        result: tt.result,
      };
      return tt.negated ? { kind: "unop", op: "!", operand: test } : test;
    }
    const op = e.operatorToken.getText(sf);
    if (LOGICAL_OPERATORS.has(op)) {
      // Truthiness has no model, and that is the input's limit, not the
      // engine's: the refusal names the operator so a body can carry it
      // as a site.
      if (!booleanShaped(e.left, scope)) {
        const failed = nonBooleanOperand(op, "the left operand", e.left, sf);
        throw new ModelError(failed.reason, failed.construct);
      }
      if (!booleanShaped(e.right, scope)) {
        const failed = nonBooleanOperand(op, "the right operand", e.right, sf);
        throw new ModelError(failed.reason, failed.construct);
      }
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
    /* v8 ignore start -- the construct scan names every operator outside
       the model before the walk reaches one; the guard keeps the walk total
       in that same voice. */
    if (!COMPARISON_OPERATORS.has(op)) {
      const unsupported = unsupportedOperator(op);
      throw new ModelError(unsupported.reason, unsupported.construct);
    }
    /* v8 ignore stop */
    if (expected !== "bool") {
      throw new ModelError(
        `operator '${op}' yields a boolean, not ${describeTy(expected)}`,
      );
    }
    return { kind: "binop", op, left, right };
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
    // An operand outside the values the model holds is refused, never
    // absorbed: a site here would have to be typed at the position — a
    // number — and stand for a string, which SameValue is false against
    // for every number there is.
    const admits = (t: ts.Expression) =>
      numericShaped(t, scope) || taggedOperand(t, scope);
    const offender = sides.findIndex((t) => !admits(t));
    if (offender !== -1) {
      const arg = unwrapParens(sides[offender]!);
      const { line, character } = sf.getLineAndCharacterOfPosition(
        arg.getStart(sf),
      );
      throw new HardRefusal(
        `'Object.is' admits numbers, booleans, union values, ` +
          `'undefined', and 'null'; argument ${offender + 1} is not one ` +
          `(${kindName(arg.kind)} at ${line + 1}:${character + 1})`,
        "Object.is",
      );
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
    // The arguments are typed before the position is, mirroring the binops.
    const args = builtin.args.map((a) => walkTyped(a, "num", scope, sf));
    if (expected !== builtin.ty) {
      throw new ModelError(
        `a call to '${builtin.name}' yields ${describeTy(builtin.ty)}, ` +
          `not ${describeTy(expected)}`,
      );
    }
    return {
      kind: "builtin",
      object: builtin.object,
      member: builtin.member,
      args,
    };
  }
  const read = builtinRead(e, scope);
  if (read !== undefined) {
    if (expected !== "num") {
      throw new ModelError(
        `a read of '${read.name}' yields a number, not ${describeTy(expected)}`,
      );
    }
    return { kind: "builtin-read", object: read.object, member: read.member };
  }
  const mcall = memberCall(e);
  if (mcall !== undefined) {
    const recv = resolveReceiver(mcall.receiver, scope, sf);
    if (
      recv !== undefined &&
      typeof recv.ty !== "string" &&
      "instance" in recv.ty
    ) {
      const ref = recv.ty.instance;
      const shape = shapeOfRef(scope, ref);
      const sig = shape.methods.get(mcall.name);
      if (sig === undefined) {
        const travelled = memberTravel(scope, ref, mcall.name);
        if (travelled !== undefined) {
          throw new ModelError(travelled.reason, travelled.construct);
        }
        throw new ModelError(
          recv.expr.kind === "self"
            ? `'this.${mcall.name}' does not name a modeled method of ` +
                `'${ref.name}'`
            : `'${displayName(ref)}' has no method '${mcall.name}' in the model`,
        );
      }
      checkArity(qualifiedName(mcall.name, ref.name), sig, mcall.args.length);
      if (expected !== sig.returns) {
        throw new ModelError(
          `a method call yields ${describeTy(sig.returns)}, not ${describeTy(expected)}`,
        );
      }
      return {
        kind: "method-call",
        className: ref.name,
        ...(ref.module !== "" ? { module: ref.module } : {}),
        name: mcall.name,
        object: recv.expr,
        args: walkArgs(mcall.args, sig, scope, sf),
      };
    }
  }
  const maccess = memberAccess(e);
  if (maccess !== undefined) {
    const recv = resolveReceiver(maccess.receiver, scope, sf);
    if (
      recv !== undefined &&
      typeof recv.ty !== "string" &&
      "instance" in recv.ty
    ) {
      const ref = recv.ty.instance;
      const shape = shapeOfRef(scope, ref);
      const module = ref.module !== "" ? { module: ref.module } : {};
      // The shape's getter set is live during the class's own walk, so a
      // forward or self-recursive getter read on `this` falls through.
      const getterTy = shape.getters.get(maccess.name);
      if (getterTy !== undefined) {
        if (expected !== getterTy) {
          throw new ModelError(
            `a member read yields ${describeTy(getterTy)}, not ${describeTy(expected)}`,
          );
        }
        return {
          kind: "getter-read",
          className: ref.name,
          ...module,
          name: maccess.name,
          object: recv.expr,
        };
      }
      const fty = shape.fields.get(maccess.name);
      if (fty === undefined) {
        const travelled = memberTravel(scope, ref, maccess.name);
        if (travelled !== undefined) {
          throw new ModelError(travelled.reason, travelled.construct);
        }
        throw new ModelError(
          recv.expr.kind === "self"
            ? `'this.${maccess.name}' does not name a field or a modeled ` +
                `getter of '${ref.name}'`
            : `'${displayName(ref)}' has no member '${maccess.name}' in the model`,
        );
      }
      // A union field at a number position was projected above; here a
      // field answers at its own type or refuses.
      const ok =
        typeof expected === "string"
          ? expected === fty
          : typeof fty !== "string" &&
            "instance" in fty &&
            sameClass(fty.instance, expected.instance);
      if (!ok) {
        throw new ModelError(
          `field '${maccess.name}' is ${describeTy(fty)}, not ${describeTy(expected)}`,
        );
      }
      return {
        kind: "field-read",
        className: ref.name,
        ...module,
        field: maccess.name,
        object: recv.expr,
      };
    }
  }
  const built = newCall(e);
  if (built !== undefined) {
    const ref = newRef(scope, built);
    // The class must exist before the instance is admitted or refused.
    const shape = classShapeOf(scope, ref);
    if (typeof expected !== "string" && sameClass(ref, expected.instance)) {
      const rawArgs = built.arguments ?? [];
      checkCtorArity(ref, shape, rawArgs.length);
      return {
        kind: "new",
        className: ref.name,
        ...(ref.module !== "" ? { module: ref.module } : {}),
        args: walkCtorArgs(rawArgs, shape, scope, sf),
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
      // An alias call at an admitted arity was claimed as the builtin
      // above, so an alias call surviving to here is one at an arity the
      // member does not take — named the way the direct spelling is.
      const aliased = scope.aliases.get(key);
      if (aliased !== undefined) {
        throw new ModelError(
          `'${aliased.name}' ${arityPhrase(aliased.arity)}`,
          aliased.name,
        );
      }
    }
    if (scope.vars.has(e.expression.text)) {
      // The model holds numbers, booleans, tagged values and instances —
      // never a callable — so calling a bound name is a shape it does not
      // follow, not a model it could not find.
      const failed = constructAt(e, e.kind, sf);
      throw new ModelError(
        `'${e.expression.text}' is a bound value, not a callable the ` +
          `model follows (${failed.reason})`,
        failed.construct,
      );
    }
    const sig = scope.mapped.get(key);
    if (sig === undefined) {
      const failed = scope.failed.get(key);
      if (failed !== undefined) {
        // A callee whose own declaration named a construct travels that
        // refusal, so the call is outside the model rather than broken.
        if (failed.construct !== undefined) {
          throw new ModelError(
            `'${name}' could not be modeled: ${failed.reason}`,
            failed.construct,
          );
        }
        throw new ModelError(`'${name}' has no model: ${failed.reason}`);
      }
      throw new ModelError(`no model registered for '${name}'`);
    }
    checkArity(name, sig, e.arguments.length);
    if (expected !== sig.returns) {
      throw new ModelError(
        `a call to '${name}' yields ${describeTy(sig.returns)}, not ${describeTy(expected)}`,
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
  // An unlisted standard-library member names itself; anything else is
  // outside the model. Both carry their construct, which is what lets a
  // body absorb them as a site rather than degrade.
  const unsupported = unsupportedBuiltin(e, scope);
  if (unsupported !== undefined) {
    throw new ModelError(unsupported.reason, unsupported.construct);
  }
  const failed = constructAt(e, e.kind, sf);
  throw new ModelError(failed.reason, failed.construct);
}

/** A member access `recv.name`. A `#`-private is a member access only
 * through `this`: TypeScript admits it nowhere else, so no other
 * receiver's private name is a shape the model reads. */
function memberAccess(
  e: ts.Expression,
): { receiver: ts.Expression; name: string } | undefined {
  const u = unwrapParens(e);
  if (!ts.isPropertyAccessExpression(u)) return undefined;
  if (
    ts.isPrivateIdentifier(u.name) &&
    unwrapParens(u.expression).kind !== ts.SyntaxKind.ThisKeyword
  ) {
    return undefined;
  }
  return { receiver: u.expression, name: u.name.text };
}

/** A member call `recv.name(args)`. */
function memberCall(e: ts.Expression):
  | {
      receiver: ts.Expression;
      name: string;
      args: readonly ts.Expression[];
    }
  | undefined {
  const u = unwrapParens(e);
  if (!ts.isCallExpression(u)) return undefined;
  const access = memberAccess(u.expression);
  return access === undefined ? undefined : { ...access, args: u.arguments };
}

/** A place's static type: an expression the walk types without an
 * expected type — a bound identifier, a fresh instance, or a field read
 * on an instance place, nested to any depth. Shape and registries only,
 * no argument walked, so the scan and the walk agree by construction. */
function placeTy(e: ts.Expression, scope: WalkScope): ValueTy | undefined {
  const u = unwrapParens(e);
  if (ts.isIdentifier(u)) {
    const ty = scope.vars.get(u.text);
    return ty === undefined || isOptionTy(ty) ? undefined : ty;
  }
  const built = newCall(u);
  if (built !== undefined) {
    const ref = newRef(scope, built);
    return classView(scope, ref) === undefined ? undefined : { instance: ref };
  }
  const access = memberAccess(u);
  if (access === undefined) return undefined;
  const recv = receiverTy(access.receiver, scope);
  if (recv === undefined || typeof recv === "string" || !("instance" in recv))
    return undefined;
  return classView(scope, recv.instance)?.shape.fields.get(access.name);
}

/** A receiver's type: a place's, or the enclosing class for `this`. A
 * bare `this` is a receiver, never a value. */
function receiverTy(e: ts.Expression, scope: WalkScope): ValueTy | undefined {
  const u = unwrapParens(e);
  /* v8 ignore next 2 -- outside a member the scan makes `this` opaque,
     so no chain rooted at one is asked about here. */
  if (u.kind === ts.SyntaxKind.ThisKeyword)
    return scope.self === undefined ? undefined : { instance: scope.self.ref };
  return placeTy(u, scope);
}

/** Whether an expression is a union-typed place. */
function isUnionPlace(e: ts.Expression, scope: WalkScope): boolean {
  const ty = placeTy(e, scope);
  return ty !== undefined && isUnionTy(ty);
}

/** Whether an expression is a union-typed place carrying the `boolean`
 * tag — the reads a boolean position projects. A union without the tag is
 * left to refuse: projecting it would throw on every path. */
function booleanUnionPlace(e: ts.Expression, scope: WalkScope): boolean {
  const ty = placeTy(e, scope);
  return ty !== undefined && isUnionTy(ty) && ty.union.includes("boolean");
}

/** A walked place: its type and its lowering. `new` arguments walk here,
 * and a member outside the model throws, exactly as a receiver arm does. */
function resolvePlace(
  e: ts.Expression,
  scope: WalkScope,
  sf: ts.SourceFile,
): { ty: ValueTy; expr: EmitExpr } | undefined {
  const u = unwrapParens(e);
  if (ts.isIdentifier(u)) {
    const ty = scope.vars.get(u.text);
    /* v8 ignore next -- an unbound name is not a place, and no body binds
       at an option; every caller has already found a place here. */
    if (ty === undefined || isOptionTy(ty)) return undefined;
    return { ty, expr: { kind: "id", name: u.text } };
  }
  const built = newCall(u);
  if (built !== undefined) {
    const ref = newRef(scope, built);
    const shape = classShapeOf(scope, ref);
    const rawArgs = built.arguments ?? [];
    checkCtorArity(ref, shape, rawArgs.length);
    return {
      ty: { instance: ref },
      expr: {
        kind: "new",
        className: ref.name,
        ...(ref.module !== "" ? { module: ref.module } : {}),
        args: walkCtorArgs(rawArgs, shape, scope, sf),
      },
    };
  }
  /* v8 ignore start -- the three shapes above are every place there is,
     and a receiver that is not an instance was already refused by the
     caller that found the place. */
  const access = memberAccess(u);
  if (access === undefined) return undefined;
  const recv = resolveReceiver(access.receiver, scope, sf);
  if (
    recv === undefined ||
    typeof recv.ty === "string" ||
    !("instance" in recv.ty)
  ) {
    return undefined;
  }
  /* v8 ignore stop */
  const ref = recv.ty.instance;
  const shape = shapeOfRef(scope, ref);
  const fty = shape.fields.get(access.name);
  if (fty === undefined) return undefined;
  return {
    ty: fty,
    expr: {
      kind: "field-read",
      className: ref.name,
      ...(ref.module !== "" ? { module: ref.module } : {}),
      field: access.name,
      object: recv.expr,
    },
  };
}

/** A walked receiver: a place, or `this` as the instance itself. */
function resolveReceiver(
  e: ts.Expression,
  scope: WalkScope,
  sf: ts.SourceFile,
): { ty: ValueTy; expr: EmitExpr } | undefined {
  const u = unwrapParens(e);
  if (u.kind === ts.SyntaxKind.ThisKeyword) {
    /* v8 ignore next -- outside a member the scan made `this` opaque. */
    if (scope.self === undefined) return undefined;
    return { ty: { instance: scope.self.ref }, expr: { kind: "self" } };
  }
  return resolvePlace(u, scope, sf);
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
    isUnionPlace(u, scope) ||
    booleanShaped(u, scope) ||
    undefAtom(u, scope) ||
    u.kind === ts.SyntaxKind.NullKeyword
  );
}

/** One side of a JsVal equality: a union place stays itself, the
 * undefined/null atoms inject at their tags, a boolean-valued shape
 * injects at 'boolean', and everything else is a number injected at
 * its. */
function eqOperand(
  e: ts.Expression,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  const u = unwrapParens(e);
  if (isUnionPlace(u, scope)) return resolvePlace(u, scope, sf)!.expr;
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
  // Strict equality reaches the tagged domain for a union place and for a
  // boolean side; the number walk keeps every other pair.
  const pulls =
    semantics === "same-value"
      ? taggedOperand
      : (e: ts.Expression, s: WalkScope) =>
          isUnionPlace(e, s) || booleanShaped(e, s);
  if (!pulls(l, scope) && !pulls(r, scope)) return undefined;
  return {
    kind: "jsval-eq",
    semantics,
    left: eqOperand(l, scope, sf),
    right: eqOperand(r, scope, sf),
  };
}

/** An expression meeting an option slot: `undefined` is `none`, an
 * instance of the slot's class is `some`, anything else is tsc's. */
function walkOptionSlot(
  e: ts.Expression,
  ref: ModelRef,
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  if (undefAtom(e, scope)) return { kind: "option" };
  return { kind: "option", expr: walkTyped(e, { instance: ref }, scope, sf) };
}

/** An expression meeting a union slot. An identical-union identifier
 * flows as itself; the `undefined`/`null` atoms inject where the union
 * carries their tag (any binding of those spellings shadows, exactly as
 * `NaN`/`Infinity` behave); a boolean-shaped expression injects at
 * `boolean`; anything that walks at `num` injects at `number`. Union
 * subtyping is out of scope: a narrower, wider, or overlapping union
 * refuses. */
function walkUnionSlot(
  e: ts.Expression,
  union: UnionTag[],
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitExpr {
  const u = unwrapParens(e);
  const bound = placeTy(u, scope);
  if (bound !== undefined && isUnionTy(bound)) {
    if (sameUnion(bound.union, union)) return resolvePlace(u, scope, sf)!.expr;
    // Widening to a superset is legal TypeScript the model does not
    // follow; any other spelling mismatch is tsc's to refuse first.
    const widening = bound.union.every((m) => union.includes(m));
    throw new ModelError(
      `'${u.getText(sf)}' is ${describeTy(bound)}, not ` +
        `${describeTy({ union })}; unions flow only between identical spellings`,
      widening ? "UnionType" : undefined,
    );
  }
  if (ts.isIdentifier(u)) {
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
  if (booleanShaped(u, scope)) {
    if (!union.includes("boolean")) {
      throw new ModelError(
        `${describeTy({ union })} slot has no 'boolean' member, so a ` +
          `boolean-valued expression cannot flow to it`,
      );
    }
    return {
      kind: "inject",
      tag: "boolean",
      expr: walkTyped(u, "bool", scope, sf),
    };
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

/** The pre-scans, in the order that fixes which failure wins — opaque
 * constructs (unsupported operators among them), then construct-failed
 * callees — each across every root before the next begins. */
function prescanFailure(
  roots: readonly ScanRoot[],
  scope: WalkScope,
): FailedDecl | undefined {
  const scans = [
    (r: ScanRoot) => findConstruct(r.expr, r.sf, scope),
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

/** A function declaration's signature check: the walked parameters, or the
 * failure that degrades the function. */
function signatureFailure(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
  reg: ParamReg,
): { params: WalkedParams; returns: ReturnTy } | FailedDecl {
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
  const returns = declaredReturnTy(fn.type, sf);
  if (typeof returns !== "string") return returns;
  return { params, returns };
}

/** The bindings in scope at a statement, parameters included: whether
 * each may be assigned and the type it was bound at, so a later declarator
 * types its initializer off an earlier binding. A branch's arm gets its
 * own copy, and a redeclaration of a name from an enclosing scope is
 * refused rather than shadowed. */
type Locals = Map<string, { mutable: boolean; ty: ValueTy }>;

/** Locals seeded from parameters, which are assignable the way
 * JavaScript has them. */
function paramLocals(params: readonly { name: string; ty: ValueTy }[]): Locals {
  return new Map(params.map((p) => [p.name, { mutable: true, ty: p.ty }]));
}

/** The types a local binding may carry: the numeric slice, a keyword
 * union riding the same tagged domain a parameter's does, or an instance
 * of a class already in the model. */
type LocalTy = "num" | "bool" | { union: UnionTag[] } | { instance: ModelRef };

/** The body as a tree of mapped statements, their expressions still tsc
 * nodes, each unmappable statement replaced by the opaque failure that
 * degrades the declaration. One node per source statement; `lowerTree`
 * truncates a path at its first return. */
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
  /** An expression statement: evaluated for its effect, value dropped. */
  | { t: "expr"; expr: ts.Expression }
  | {
      t: "if";
      cond: { expr: ts.Expression } | { opaque: FailedDecl };
      then: TStmt[];
      else?: TStmt[];
    }
  | { t: "opaque"; failure: FailedDecl };

/** The error kind a `throw` carries: the constructor's name. The message is
 * discarded — the model distinguishes throws by kind alone. */
function errorKind(e: ts.Expression): string | undefined {
  const inner = unwrapParens(e);
  if (!ts.isNewExpression(inner)) return undefined;
  if (!ts.isIdentifier(inner.expression)) return undefined;
  return inner.expression.text;
}

/** A local declarator's admitted type: its initializer's static type
 * when there is no annotation, the numeric slice for `number`, a class
 * resolved exactly as a field's is (a degraded class is the failure that
 * travels), or a keyword union normalized exactly as a parameter's is
 * (`localValueTy` and `paramValueTy` share `keywordTags` and
 * `normalizedUnion`, so the two spellings can never drift). Anything
 * else — a later-declared class, a lone non-number keyword, a union with
 * a member outside the keywords — keeps the declarator's degradation. */
function localValueTy(
  d: ts.VariableDeclaration,
  sf: ts.SourceFile,
  reg: ParamReg,
  scope: WalkScope,
): LocalTy | FailedDecl | undefined {
  const t = d.type;
  if (t === undefined) return inferredLocalTy(d.initializer!, scope, reg);
  if (t.kind === ts.SyntaxKind.NumberKeyword) return "num";
  if (t.kind === ts.SyntaxKind.BooleanKeyword) return "bool";
  const cls = classRefTy(t, reg);
  if (cls !== undefined) return cls;
  if (!ts.isUnionTypeNode(t)) return undefined;
  const tags = keywordTags(t);
  if (!Array.isArray(tags)) return undefined;
  const ty = normalizedUnion(tags, t, sf);
  return typeof ty === "string" || "union" in ty ? ty : undefined;
}

/** An unannotated declarator's type: a construction's class, resolved
 * exactly as an annotation naming it would be (a later class refuses the
 * statement, a degraded one travels its reason); the class or union any
 * other place is at — a bound identifier, a field read on an instance
 * place; and `number` for every other initializer, which the typed walk
 * then holds to a number. An explicit annotation never comes here. */
function inferredLocalTy(
  init: ts.Expression,
  scope: WalkScope,
  reg: ParamReg,
): LocalTy | FailedDecl | undefined {
  const built = newCall(init);
  if (built !== undefined)
    return classNamed((built.expression as ts.Identifier).text, reg);
  // A place answers at its own type before the shape test, which reads a
  // boolean-carrying union place as a boolean: `const w = this.on` is the
  // union, the type TypeScript infers for it.
  const ty = placeTy(init, scope);
  /* v8 ignore next -- no place is an option: a bound option is not a
     place, and no field holds one. */
  if (ty !== undefined && !isOptionTy(ty)) return ty;
  return booleanShaped(init, scope) ? "bool" : "num";
}

/** A declaration's `TStmt`s, or undefined when any declarator falls
 * outside the slice — `var`, `using`, destructuring, an uninitialized
 * `let`, a type annotation that is neither `number`, a modeled class, nor
 * a keyword union, or a redeclaration of a name already bound here. A
 * declarator at a degraded class is instead the opaque statement carrying
 * that class's own failure. Locals set for earlier declarators persist
 * even when a later one fails, so the scans that follow still see them. */
function declStmts(
  s: ts.VariableStatement,
  locals: Locals,
  sf: ts.SourceFile,
  scope: WalkScope,
): TStmt[] | undefined {
  const flags = s.declarationList.flags;
  const isConst = (flags & ts.NodeFlags.Const) !== 0;
  const isLet = (flags & ts.NodeFlags.Let) !== 0;
  if (!isConst && !isLet) return undefined;
  if ((flags & ts.NodeFlags.Using) !== 0) return undefined;
  if (s.declarationList.declarations.length === 0) return undefined;
  const reg: ParamReg = {
    classes: scope.classes,
    failed: scope.failed,
    names: scope.names,
    module: scope.module,
    ...(scope.self !== undefined ? { self: scope.self.ref } : {}),
    unions: true,
    booleans: true,
  };
  const stmts: TStmt[] = [];
  for (const d of s.declarationList.declarations) {
    if (!ts.isIdentifier(d.name)) return undefined;
    if (d.initializer === undefined) return undefined;
    // Each declarator types its initializer off the bindings before it,
    // the earlier declarators of its own list included.
    const bound: WalkScope = {
      ...scope,
      vars: new Map([...locals].map(([n, l]) => [n, l.ty])),
    };
    const ty = localValueTy(d, sf, reg, bound);
    if (ty === undefined) return undefined;
    if (typeof ty !== "string" && "reason" in ty)
      return [{ t: "opaque", failure: ty }];
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
    locals.set(d.name.text, { mutable: !isConst, ty });
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
  if (locals.get(target.text)?.mutable !== true) return undefined;
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

/** One statement's `TStmt`s. Whatever the slice cannot say falls through
 * to an opaque node carrying the construct that stopped it. */
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
    const stmts = declStmts(s, locals, sf, scope);
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
    // A statement that assigns is not a site: the model would lose the
    // write. Anything else runs for its effect, value dropped.
    const mutated = containsMutation(s.expression);
    if (mutated !== undefined) {
      return [
        { t: "opaque", failure: modelFailure(mutationRefusal(mutated, sf)) },
      ];
    }
    return [{ t: "expr", expr: s.expression }];
  }
  if (ts.isIfStatement(s)) {
    const inner = unwrapParens(s.expression);
    // The condition must be boolean-shaped — a comparison, an `Object.is`
    // call, or a logical combination of them: truthiness has no model. A
    // standard-library member the model cannot take names itself here as
    // it does anywhere else; only truthiness is left to the syntax kind.
    // The scan types a bound name off the same binding the walk will, so
    // a boolean local is a condition here exactly as it is in the walk.
    const bound: WalkScope = {
      ...scope,
      vars: new Map([...locals].map(([n, l]) => [n, l.ty])),
    };
    const cond = booleanShaped(inner, bound)
      ? { expr: inner }
      : {
          opaque:
            unsupportedBuiltin(inner, bound) ??
            constructAt(inner, inner.kind, sf),
        };
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
 * list. It exists for two observable effects: the order errors are
 * discovered in, and the tail statements it yields exactly once. */
type Cont = () => void;

/** Lowers a statement tree into the emitted statement list, walking every
 * expression in tree order so the first failure — and its message — is
 * fixed by the source. A return or throw ends its path (what follows never
 * reaches the artifact); a branch's tail is validated once and stays after
 * the branch — do-notation needs no join. */
function lowerTree(
  stmts: readonly TStmt[],
  vars: readonly (readonly [string, ValueTy])[],
  k: Cont,
  scope: WalkScope,
  sf: ts.SourceFile,
  returns: ReturnTy,
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
      return [{ kind: "return", expr: walk(s.expr, returns, vars) }];
    case "throw":
      return [{ kind: "throw", error: s.error }];
    case "decl": {
      // A binding whose scope is the rest of the list; a bind rather than
      // a substitution, so an unused initializer still evaluates. A union
      // or class local's initializer meets its declared type as a slot,
      // exactly as an argument meets such a parameter's.
      const init = walk(s.init, s.ty, vars);
      const tail = lowerTree(
        rest,
        [...vars, [s.name, s.ty] as const],
        k,
        scope,
        sf,
        returns,
      );
      return [
        {
          kind: s.mutable ? "let" : "const",
          name: s.name,
          init,
          ...bindingTy(s.ty),
        },
        ...tail,
      ];
    }
    case "assign": {
      // A reassignment is typed at what the target was bound at — a
      // parameter's or a union local's type included.
      const target = vars.find(([n]) => n === s.name)?.[1] ?? "num";
      const expr = walk(s.expr, target, vars);
      const tail = lowerTree(rest, vars, k, scope, sf, returns);
      return [{ kind: "assign", name: s.name, expr }, ...tail];
    }
    case "field-set": {
      // The right side meets the field's declared type as a slot: a
      // union field injects, an instance field takes an instance.
      const ty = scope.ctorFields?.get(s.field) ?? "num";
      const expr = walk(s.expr, ty, vars);
      const tail = lowerTree(rest, vars, k, scope, sf, returns);
      return [{ kind: "field-set", field: s.field, expr }, ...tail];
    }
    /* v8 ignore start -- an opaque statement is unreachable here: the
       statement scan already degraded the declaration. The throw is a
       defense, so a scan regression becomes a contained failure rather
       than a bad artifact. */
    case "opaque":
      throw new ModelError(s.failure.reason, s.failure.construct);
    /* v8 ignore stop */
    case "expr": {
      // The value is dropped, the effect is not. The position expects
      // whatever the expression's own shape suggests, since there is no
      // unit codomain to type it at.
      const bound: WalkScope = { ...scope, vars: new Map(vars) };
      const expected: Expected = booleanShaped(s.expr, bound)
        ? "bool"
        : (callReturns(s.expr, bound) ?? "num");
      const expr = walk(s.expr, expected, vars);
      const tail = lowerTree(rest, vars, k, scope, sf, returns);
      return [{ kind: "discard", expr }, ...tail];
    }
    case "if": {
      // A condition the model cannot read is a site like any other: it is
      // evaluated on every path, and it may throw.
      const cond: EmitExpr =
        "opaque" in s.cond
          ? residualAt(
              new ModelError(s.cond.opaque.reason, s.cond.opaque.construct),
              "bool",
              { ...scope, vars: new Map(vars) },
            )
          : walk(s.cond.expr, "bool", vars);
      const elseArm = s.else ?? [];
      // What an arm that falls through continues into: the rest of this
      // list, and only then the enclosing continuation.
      let tail: EmitStmt[] = [];
      let tailBuilt = false;
      const after: Cont = () => {
        /* v8 ignore next -- at most one arm reaches this continuation, so
           the flag never fires; it holds the yields-once invariant even
           if that changes. */
        if (tailBuilt) return;
        tailBuilt = true;
        tail = lowerTree(rest, vars, k, scope, sf, returns);
      };
      /* v8 ignore start -- the continuation an arm that leaves can never
         invoke: `stmtsLeave` already proved it returns or throws, so this
         exists only to fail loudly if that analysis is wrong. */
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
        // Both arms fall through, so the tail is the join both reach: it
        // is validated before either arm, and only once.
        after();
        thenK = () => {};
        elseK = () => {};
      }
      const thenIR = lowerTree(s.then, vars, thenK, scope, sf, returns);
      const elseIR = lowerTree(elseArm, vars, elseK, scope, sf, returns);
      const stmt: EmitStmt =
        s.else !== undefined && elseIR.length > 0
          ? { kind: "if", cond, then: thenIR, else: elseIR }
          : { kind: "if", cond, then: thenIR };
      return deadTail ? [stmt] : [stmt, ...tail];
    }
  }
}

/** The first statement outside the slice, arms included — the one failure
 * a body still degrades on, now that its expressions carry their own as
 * residual sites. Dead code counts: a statement the model cannot map is
 * not made mappable by being unreachable. */
function treeStatementFailure(stmts: readonly TStmt[]): FailedDecl | undefined {
  for (const s of stmts) {
    if (s.t === "opaque") return s.failure;
    if (s.t === "if") {
      const found =
        treeStatementFailure(s.then) ??
        (s.else !== undefined ? treeStatementFailure(s.else) : undefined);
      if (found !== undefined) return found;
    }
  }
  return undefined;
}

/** The names a statement tree assigns anywhere, arms included. */
function assignedIn(
  stmts: readonly TStmt[],
  into = new Set<string>(),
): Set<string> {
  for (const s of stmts) {
    if (s.t === "assign") into.add(s.name);
    else if (s.t === "if") {
      assignedIn(s.then, into);
      if (s.else !== undefined) assignedIn(s.else, into);
    }
  }
  return into;
}

function defaultFailure(name: string, reason: string): string {
  return `parameter '${name}' has a default the model cannot evaluate: ${reason}`;
}

/** The `type` a binding at `ty` carries on the wire: absent for the
 * numeric slice, `"boolean"` for a boolean, the tag array for a union,
 * the class for an instance. */
function bindingTy(ty: ValueTy): {
  type?: UnionTag[] | { class: string; module?: string } | "boolean";
} {
  if (ty === "num") return {};
  if (ty === "bool") return { type: "boolean" };
  if ("union" in ty) return { type: [...ty.union] };
  /* v8 ignore next -- a body never binds at an option; the opening is T */
  if ("option" in ty) return {};
  const { module, name } = ty.instance;
  return { type: { class: name, ...(module !== "" ? { module } : {}) } };
}

/** The statements a body opens with: each defaulted parameter rebound at
 * its declared type to its initializer when the slot holds `undefined`.
 * JavaScript resolves defaults after every argument, left to right, with
 * earlier parameters in scope — which is what statements in declaration
 * order at the top of the body denote. */
function defaultOpenings(
  params: WalkedParams,
  tree: readonly TStmt[],
  scope: WalkScope,
  sf: ts.SourceFile,
): EmitStmt[] {
  const assigned = assignedIn(tree);
  const out: EmitStmt[] = [];
  params.forEach((p, i) => {
    if (p.init === undefined) return;
    const initScope: WalkScope = {
      ...scope,
      vars: new Map(params.slice(0, i).map((q) => [q.name, q.ty])),
      // The same sink, so a default's site numbers in sequence with the
      // body's, and its text reads as the parameter's failure.
      ...(scope.residuals === undefined
        ? {}
        : {
            residuals: {
              ...scope.residuals,
              wrap: (reason: string) => defaultFailure(p.name, reason),
            },
          }),
    };
    let init: EmitExpr;
    try {
      init = walkTyped(p.init, p.ty, initScope, sf);
    } catch (err) {
      /* v8 ignore next -- the walk throws nothing else */
      if (!(err instanceof ModelError)) throw err;
      throw new ModelError(defaultFailure(p.name, err.message), err.construct);
    }
    const slot: EmitExpr = { kind: "id", name: p.name };
    // A class default's slot is an option, tested and projected on its
    // own; every other slot lives in the tagged domain.
    const optional = isOptionTy(p.slot);
    const cond: EmitExpr = optional
      ? { kind: "option-test", expr: slot, present: false }
      : {
          kind: "jsval-eq",
          semantics: "strict",
          left: slot,
          right: { kind: "inject", tag: "undefined" },
        };
    const fallthrough: EmitExpr = optional
      ? { kind: "option-get", expr: slot }
      : p.ty === "num"
        ? { kind: "project", tag: "number", expr: slot }
        : p.ty === "bool"
          ? { kind: "project", tag: "boolean", expr: slot }
          : slot;
    out.push({
      kind: assigned.has(p.name) ? "let" : "const",
      name: p.name,
      init: { kind: "cond", cond, then: init, else: fallthrough },
      ...bindingTy(p.ty),
    });
  });
  return out;
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

/** A free function's parameter shape: the shared rule, optionals admitted. */
function fnParamFailure(
  p: ts.ParameterDeclaration,
  sf: ts.SourceFile,
): FailedDecl | undefined {
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
  /** Whether a bare `boolean` is admitted here: free functions and
   * methods take it, a constructor and a field keep their refusal. */
  booleans: boolean;
}

/** A declared return type: number, or boolean; anything else is the
 * failure that degrades the declaration. */
function declaredReturnTy(
  t: ts.TypeNode,
  sf: ts.SourceFile,
): ReturnTy | FailedDecl {
  if (t.kind === ts.SyntaxKind.NumberKeyword) return "num";
  if (t.kind === ts.SyntaxKind.BooleanKeyword) return "bool";
  return constructAt(t, t.kind, sf);
}

/** The `returns` a declaration carries on the wire: absent for number. */
function wireReturns(returns: ReturnTy): { returns?: "boolean" } {
  return returns === "bool" ? { returns: "boolean" } : {};
}

/** A declared type node's value type — a parameter's or a field's: a
 * number, a boolean (where `reg.booleans` admits it), a class already in
 * the model, or (where `reg.unions` admits it) a keyword union; anything
 * else is the failure that degrades the declaration. A class resolves
 * under the source-order discipline member calls follow, and one that
 * degraded travels its own failure. */
function declaredValueTy(
  t: ts.TypeNode,
  sf: ts.SourceFile,
  reg: ParamReg,
): ValueTy | FailedDecl {
  if (t.kind === ts.SyntaxKind.NumberKeyword) return "num";
  if (t.kind === ts.SyntaxKind.BooleanKeyword && reg.booleans) return "bool";
  const cls = classRefTy(t, reg);
  if (cls !== undefined) return cls;
  // A keyword union normalizes to its deduplicated tags; a member outside
  // the keywords refuses at that member, not at the union.
  if (ts.isUnionTypeNode(t) && reg.unions) {
    const tags = keywordTags(t);
    if (!Array.isArray(tags)) return constructAt(tags, tags.kind, sf);
    return normalizedUnion(tags, t, sf);
  }
  return constructAt(t, t.kind, sf);
}

/** A bare type reference resolved as a class under the source-order
 * discipline: the instance for a class already in the model (`self`
 * included), the travelling failure for one that degraded, and undefined
 * for anything else — a later-declared class, a type argument, a
 * non-reference node — which the caller refuses in its own terms. */
function classRefTy(
  t: ts.TypeNode,
  reg: ParamReg,
): { instance: ModelRef } | FailedDecl | undefined {
  if (
    !ts.isTypeReferenceNode(t) ||
    !ts.isIdentifier(t.typeName) ||
    t.typeArguments !== undefined
  )
    return undefined;
  return classNamed(t.typeName.text, reg);
}

/** A class spelling resolved under the source-order discipline: the
 * instance for a class already in the model (`self` included), the
 * travelling failure for one that degraded, and undefined for a
 * later-declared one. */
function classNamed(
  spelling: string,
  reg: ParamReg,
): { instance: ModelRef } | FailedDecl | undefined {
  const ref = reg.names.get(spelling) ?? { module: reg.module, name: spelling };
  if (reg.self !== undefined && sameClass(ref, reg.self))
    return { instance: ref };
  if (reg.classes.has(modelKey(ref))) return { instance: ref };
  const failed = reg.failed.get(modelKey(ref));
  if (failed === undefined) return undefined;
  return {
    ...(failed.construct !== undefined ? { construct: failed.construct } : {}),
    reason: `'${displayName(ref)}' could not be modeled: ${failed.reason}`,
  };
}

/** A parameter's declared type, or the failure that degrades the
 * declaration. */
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
  return declaredValueTy(t, sf, reg);
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

/** A walked parameter: its declared type `ty` (what the body binds), the
 * `slot` a call fills (the declared type widened by `undefined` when an
 * initializer makes the argument optional), and the initializer itself. */
type WalkedParam = {
  name: string;
  ty: ValueTy;
  slot: ValueTy;
  optional: boolean;
  init?: ts.Expression;
};
type WalkedParams = WalkedParam[];

/** The boundary type a defaulted parameter presents to callers. The
 * tagged domain has no instance tag, so a class default takes an option
 * of that class instead. */
function boundaryTy(ty: ValueTy): ValueTy {
  if (ty === "num") return { union: ["number", "undefined"] };
  if (ty === "bool") return { union: ["boolean", "undefined"] };
  if ("union" in ty) {
    const tags = UNION_TAGS.filter(
      (t) => ty.union.includes(t) || t === "undefined",
    );
    return { union: [...tags] };
  }
  /* v8 ignore next -- a walked parameter's type is never already an option */
  if ("option" in ty) return ty;
  return { option: ty.instance };
}

/** Names and types for a parameter list, or the first failure. The shape
 * check leads: a parameter the caller's `shapeFailure` rejects has no
 * type worth asking about. */
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
    // one position to land in. tsc refuses this first; the walk re-checks
    // so the lowering never leans on an unverified invariant.
    if (seenOptional && !optional) return constructAt(p, p.kind, sf);
    seenOptional ||= optional;
    const ty = paramValueTy(p, sf, reg);
    if (typeof ty !== "string" && "reason" in ty) return ty;
    const init = p.initializer;
    const slot = init === undefined ? ty : boundaryTy(ty);
    out.push({
      name: (p.name as ts.Identifier).text,
      ty,
      slot,
      optional,
      ...(init !== undefined ? { init } : {}),
    });
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
  /** Every member's residual sites, in the order the members are walked:
   * the constructor's, then each getter's, then each method's. */
  residuals: EmitResidualDecl[];
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

  const fields = new Map<string, ValueTy>();
  // A field's type resolves as a parameter's does, the class itself not
  // yet registered, so a self-typed field refuses like a self-typed
  // constructor parameter.
  const fieldReg: ParamReg = {
    classes: c.classes,
    failed: c.failed,
    names,
    module: qualifier,
    unions: true,
    booleans: true,
  };
  const ctors: ts.ConstructorDeclaration[] = [];
  const getterDecls: ts.GetAccessorDeclaration[] = [];
  const getterReturns = new Map<string, ReturnTy>();
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
      const ty = declaredValueTy(m.type, sf, fieldReg);
      if (typeof ty !== "string" && "reason" in ty) return ty;
      if (RESERVED_MEMBERS.has(spelling))
        return memberNameFailure(className, spelling, "reserves the name");
      if (fields.has(spelling))
        return memberNameFailure(className, spelling, "declares two fields");
      fields.set(spelling, ty);
      continue;
    }
    if (ts.isGetAccessorDeclaration(m)) {
      const walked = getterFailure(m, className, spelling, sf);
      if (!("returns" in walked)) memberFailed.set(memberKey(spelling), walked);
      else {
        getterDecls.push(m);
        getterReturns.set(spelling, walked.returns);
      }
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
    if (fields.has(spelling))
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
    if (fields.has(spelling))
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
    booleans: true,
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
  const residuals: EmitResidualDecl[] = [];
  /** A member's sink. `self` is set for a getter or a method, whose sites
   * take the receiver first; a constructor has no instance yet. */
  const sinkFor = (member: string, receiver: boolean): ResidualSink => ({
    owner: qualifiedName(member, className),
    module: qualifier,
    sites: residuals,
    ...(receiver
      ? {
          self: {
            param: {
              name: "self",
              type: {
                class: className,
                ...(qualifier !== "" ? { module: qualifier } : {}),
              },
            },
            expr: { kind: "self" },
          },
        }
      : {}),
  });
  const ctorScope: WalkScope = {
    ...base,
    vars: new Map(ctorParams.map((p) => [p.name, p.ty])),
    ctorFields: fields,
    residuals: sinkFor("constructor", false),
  };
  const fieldSet = new Set(fields.keys());
  const ctorLocals = paramLocals(ctorParams);
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
      const missing = [...fields.keys()].find((f) => !assigned.has(f));
      if (missing !== undefined) {
        return {
          construct: "constructor",
          reason:
            `the constructor of '${className}' never assigns field ` +
            `'${missing}'; ${PRECONDITION}`,
        };
      }
    }
    const failure = treeStatementFailure(tree);
    if (failure !== undefined) return failure;
    // Falling off the end is a constructor's normal exit: the renderer
    // appends the instance return.
    const openings = defaultOpenings(ctorParams, tree, ctorScope, sf);
    ctorBody = [
      ...openings,
      ...lowerTree(
        tree,
        ctorParams.map((p) => [p.name, p.ty] as const),
        () => {},
        ctorScope,
        sf,
        "num",
      ),
    ];
  } catch (err) {
    if (err instanceof CtorPrecondition)
      return { construct: "constructor", reason: err.message };
    /* v8 ignore next -- the walk throws nothing else */
    if (!(err instanceof ModelError)) throw err;
    return modelFailure(err);
  }

  // `ctorReg` bans declared unions, so this restates the ban where the
  // shape is recorded rather than trusting the flag everywhere
  // downstream. A defaulted parameter's slot is a union all the same:
  // the ban is on what the source declares, not on the boundary.
  const shapeCtorParams: ValueTy[] = [];
  for (const p of ctorParams) {
    /* v8 ignore start -- unreachable: ctorReg refused the union first. */
    if (typeof p.ty !== "string" && "union" in p.ty)
      return constructAt(ctor, ctor.kind, sf);
    /* v8 ignore stop */
    shapeCtorParams.push(p.slot);
  }

  // Both registries fill as members render, so a member body sees only
  // the siblings ahead of it: a forward reference degrades the reader.
  const modeledGetters = new Map<string, ReturnTy>();
  const methodSigs = new Map<string, FnSig>();
  const shape: ClassShape = {
    fields,
    getters: modeledGetters,
    ctorParams: shapeCtorParams,
    ctorParamNames: ctorParams.map((p) => p.name),
    ctorRequired:
      ctorParams.map((p) => p.init !== undefined).lastIndexOf(false) + 1,
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
      residuals: sinkFor(spelling, true),
    };
    const body = g.body!.statements.flatMap((st) =>
      structureStmt(st, sf, new Map(), scope),
    );
    const failure = treeStatementFailure(body);
    if (failure !== undefined) {
      memberFailed.set(memberKey(spelling), failure);
      continue;
    }
    const returns = getterReturns.get(spelling)!;
    try {
      getters.push({
        name: spelling,
        ...wireReturns(returns),
        body: lowerTree(
          body,
          [],
          () => {
            throw new ModelError("the body must return on every path");
          },
          scope,
          sf,
          returns,
        ),
      });
      modeledGetters.set(spelling, returns);
    } catch (err) {
      /* v8 ignore next -- the walk throws nothing else */
      if (!(err instanceof ModelError)) throw err;
      memberFailed.set(memberKey(spelling), modelFailure(err));
    }
  }
  // Getters render ahead of methods, so a getter body sees an empty
  // method map: a getter calling a method degrades alone.
  const methodReg: ParamReg = {
    ...ctorReg,
    unions: true,
    booleans: true,
    self: self.ref,
  };
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
    const returns = walked.returns;
    const scope: WalkScope = {
      ...base,
      vars: new Map(params.map((p) => [p.name, p.ty])),
      self,
      selfFailed: memberFailed,
      residuals: sinkFor(spelling, true),
    };
    const locals = paramLocals(params);
    const body = m.body!.statements.flatMap((st) =>
      structureStmt(st, sf, locals, scope),
    );
    const prescan = treeStatementFailure(body);
    if (prescan !== undefined) {
      memberFailed.set(memberKey(spelling), prescan);
      continue;
    }
    try {
      const openings = defaultOpenings(params, body, scope, sf);
      methods.push({
        name: spelling,
        params: params.map((p) => wireParam(p.name, p.slot)),
        ...wireReturns(returns),
        body: [
          ...openings,
          ...lowerTree(
            body,
            params.map((p) => [p.name, p.ty] as const),
            () => {
              throw new ModelError("the body must return on every path");
            },
            scope,
            sf,
            returns,
          ),
        ],
      });
      methodSigs.set(spelling, sigOf(params, returns));
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
      fields: [...fields].map(([name, ty]) => ({ name, ...bindingTy(ty) })),
      ctor: {
        params: ctorParams.map((p) => wireParam(p.name, p.slot)),
        body: ctorBody,
      },
      getters,
      methods,
    },
    shape,
    memberFailed,
    residuals,
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
): { params: WalkedParams; returns: ReturnTy } | FailedDecl {
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
  const returns = declaredReturnTy(m.type, sf);
  if (typeof returns !== "string") return returns;
  return { params, returns };
}

/** A getter outside the slice degrades alone: privacy, a signature the
 * model cannot read, or a name the model reserves. */
function getterFailure(
  g: ts.GetAccessorDeclaration,
  className: string,
  spelling: string,
  sf: ts.SourceFile,
): { returns: ReturnTy } | FailedDecl {
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
  const returns = declaredReturnTy(g.type, sf);
  if (typeof returns !== "string") return returns;
  return { returns };
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
):
  | { emit: EmitFunction; sig: FnSig; residuals: EmitResidualDecl[] }
  | FailedDecl {
  const sig = signatureFailure(fn, sf, {
    classes: c.classes,
    failed: c.failed,
    names,
    module,
    unions: true,
    booleans: true,
  });
  if (!("params" in sig)) return sig;
  const params = sig.params;
  const returns = sig.returns;
  const residuals: EmitResidualDecl[] = [];
  const scope: WalkScope = {
    vars: new Map(params.map((p) => [p.name, p.ty])),
    mapped: c.mapped,
    failed: c.failed,
    classes: c.classes,
    constants: c.constants,
    aliases: c.aliases,
    names,
    module,
    residuals: { owner: fn.name!.text, module, sites: residuals },
  };
  const locals = paramLocals(params);
  const tree = fn.body!.statements.flatMap((s) =>
    structureStmt(s, sf, locals, scope),
  );
  const statementFailure = treeStatementFailure(tree);
  if (statementFailure !== undefined) return statementFailure;
  try {
    const openings = defaultOpenings(params, tree, scope, sf);
    const body = [
      ...openings,
      ...lowerTree(
        tree,
        params.map((p) => [p.name, p.ty] as const),
        () => {
          // A `number` function that runs off the end returns undefined,
          // which this slice has no value for.
          throw new ModelError("the body must return on every path");
        },
        scope,
        sf,
        returns,
      ),
    ];
    return {
      emit: {
        kind: "function",
        name: fn.name!.text,
        ...(module !== "" ? { module } : {}),
        params: params.map((p) => wireParam(p.name, p.slot)),
        ...wireReturns(returns),
        source: fn.getText(sf),
        body,
      },
      sig: sigOf(params, returns),
      residuals,
    };
  } catch (err) {
    if (err instanceof ModelError) return modelFailure(err);
    /* v8 ignore next 2 -- the walk throws nothing else */
    throw err;
  }
}

/** Parse one formula atom: wrapped in parentheses so it parses as an
 * expression, rejected on any parser diagnostic. */
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

/** How many arguments a builtin admits: a floor, and a ceiling when it
 * has one. A fixed-arity member sets both. */
interface Arity {
  min: number;
  max?: number;
}

/** Whether a call site's argument count is one the member admits. */
function admitsArity(arity: Arity, got: number): boolean {
  return got >= arity.min && (arity.max === undefined || got <= arity.max);
}

/** A small count as a word, the spelling the diagnostics use. */
function countWord(n: number): string {
  /* v8 ignore next 2 -- every whitelisted arity is inside the list; a
     larger one would still read, as a digit. */
  return ["no", "one", "two", "three"][n] ?? `${n}`;
}

/** How a member's admitted arity reads in a refusal. Only a fixed-arity
 * member can be refused for its count — the variadic ones admit every
 * arity — so the floor-only and range spellings are here for a future
 * member, not for anything the whitelist has today. */
function arityPhrase(arity: Arity): string {
  /* v8 ignore next -- every fixed-arity member the whitelist has is unary,
     so only the singular is ever spelled. */
  const noun = (n: number) => (n === 1 ? "argument" : "arguments");
  /* v8 ignore start */
  if (arity.max === undefined) {
    return `takes at least ${countWord(arity.min)} ${noun(arity.min)}`;
  }
  if (arity.min !== arity.max) {
    return (
      `takes between ${countWord(arity.min)} and ` +
      `${countWord(arity.max)} arguments`
    );
  }
  /* v8 ignore stop */
  return `takes ${countWord(arity.min)} ${noun(arity.min)}`;
}

/** A whitelisted builtin as a use site needs it: the source spelling
 * (for messages), the standard-library object and member it names, the
 * arity the model admits, and the value type it yields. */
interface BuiltinEntry {
  name: string;
  object: string;
  member: string;
  arity: Arity;
  ty: Expected;
}

/** The standard-library objects whose member calls the model reads. */
const BUILTIN_OBJECTS: ReadonlySet<string> = new Set(["Math", "Number"]);

/** The arity of a member that takes exactly one argument. */
const UNARY: Arity = { min: 1, max: 1 };

/** The arity of a member whose call site fixes the count: `Math.min` and
 * `Math.max` reduce over their arguments, so every count is one they
 * admit, the empty call included — it is their identity. */
const VARIADIC: Arity = { min: 0 };

/** The builtin member calls with models, keyed by source spelling. The
 * objects are immutable in the standard library, so each entry is a fixed
 * primitive; any other member of these objects is unsupported. */
const BUILTIN_MEMBER_CALLS: ReadonlyMap<string, BuiltinEntry> = new Map(
  (
    [
      ["Math", "sqrt", "num", UNARY],
      ["Math", "abs", "num", UNARY],
      ["Math", "trunc", "num", UNARY],
      ["Math", "floor", "num", UNARY],
      ["Math", "ceil", "num", UNARY],
      ["Math", "round", "num", UNARY],
      ["Math", "sign", "num", UNARY],
      ["Math", "fround", "num", UNARY],
      ["Math", "min", "num", VARIADIC],
      ["Math", "max", "num", VARIADIC],
      ["Number", "isFinite", "bool", UNARY],
      ["Number", "isNaN", "bool", UNARY],
      ["Number", "isInteger", "bool", UNARY],
      ["Number", "isSafeInteger", "bool", UNARY],
    ] as const
  ).map(([object, member, ty, arity]) => [
    `${object}.${member}`,
    { name: `${object}.${member}`, object, member, arity, ty },
  ]),
);

/** A whitelisted builtin as a read site needs it: the source spelling
 * and the object and member it names. Every read is one of the Number
 * constants the standard fixes, so it has no arity and yields a number. */
interface BuiltinReadEntry {
  name: string;
  object: string;
  member: string;
}

/** The builtin member reads with models: the Number values ECMA-262 fixes
 * as own properties of `Math` and `Number`, keyed by source spelling. The
 * Js library defines each under that spelling. */
const BUILTIN_MEMBER_READS: ReadonlyMap<string, BuiltinReadEntry> = new Map(
  (
    [
      ["Number", "EPSILON"],
      ["Number", "MAX_SAFE_INTEGER"],
      ["Number", "MIN_SAFE_INTEGER"],
      ["Number", "MAX_VALUE"],
      ["Number", "MIN_VALUE"],
      ["Number", "POSITIVE_INFINITY"],
      ["Number", "NEGATIVE_INFINITY"],
      ["Number", "NaN"],
      ["Math", "E"],
      ["Math", "LN10"],
      ["Math", "LN2"],
      ["Math", "LOG10E"],
      ["Math", "LOG2E"],
      ["Math", "PI"],
      ["Math", "SQRT1_2"],
      ["Math", "SQRT2"],
    ] as const
  ).map(([object, member]) => [
    `${object}.${member}`,
    { name: `${object}.${member}`, object, member },
  ]),
);

/** The `Math.m`/`Number.m` spelling an expression reads from the standard
 * library, if it is one, under a shadowing rule: a binding of the
 * object's name wins over the builtin, the way one wins over the
 * `NaN`/`Infinity` atoms, so the model never states a claim about the
 * standard library the source does not make. The rule is the caller's —
 * a body's or a module scope's — so the two cannot drift apart. */
function builtinSpelling(
  e: ts.Expression,
  binds: (name: string) => boolean,
): string | undefined {
  if (!ts.isPropertyAccessExpression(e) || !ts.isIdentifier(e.expression)) {
    return undefined;
  }
  const object = e.expression.text;
  if (!BUILTIN_OBJECTS.has(object)) return undefined;
  if (binds(object)) return undefined;
  return `${object}.${e.name.text}`;
}

/** A body's shadowing rule: a parameter, a local, or anything the module
 * binds — declaration or import, degraded ones included. */
function bodyBinds(scope: WalkScope): (name: string) => boolean {
  return (name) => scope.vars.has(name) || moduleBinds(scope, name);
}

/** The whitelisted builtin member read an expression is, if any. The call
 * recognizers answer first at every site, so a read here is a value. */
function builtinRead(
  e: ts.Expression,
  scope: WalkScope,
): BuiltinReadEntry | undefined {
  const spelled = builtinSpelling(e, bodyBinds(scope));
  return spelled === undefined ? undefined : BUILTIN_MEMBER_READS.get(spelled);
}

/** A standard-library member the model cannot take, named: a call of a
 * member the calls table does not cover, a listed call at an arity it
 * does not admit, a read of a member the reads table does not cover —
 * and, across the tables, a call member read as a value or a read member
 * called. The source wrote a real API, so the failure says which, rather
 * than degrading to a syntax kind. */
function unsupportedBuiltin(
  e: ts.Expression,
  scope: WalkScope,
): FailedDecl | undefined {
  const binds = bodyBinds(scope);
  if (ts.isCallExpression(e)) {
    const spelled = builtinSpelling(e.expression, binds);
    if (spelled === undefined) return undefined;
    const entry = BUILTIN_MEMBER_CALLS.get(spelled);
    if (entry === undefined) {
      return {
        construct: spelled,
        reason: BUILTIN_MEMBER_READS.has(spelled)
          ? `'${spelled}' is modeled only as a read`
          : `'${spelled}' is not supported`,
      };
    }
    if (admitsArity(entry.arity, e.arguments.length)) return undefined;
    return {
      construct: spelled,
      reason: `'${spelled}' ${arityPhrase(entry.arity)}`,
    };
  }
  const spelled = builtinSpelling(e, binds);
  if (spelled === undefined || BUILTIN_MEMBER_READS.has(spelled)) {
    return undefined;
  }
  return {
    construct: spelled,
    reason: BUILTIN_MEMBER_CALLS.has(spelled)
      ? `'${spelled}' is modeled only as a callee`
      : `'${spelled}' is not supported`,
  };
}

/** The whitelisted builtin member call an expression is, if any, with
 * its arguments. A call through a module-level alias lowers as the
 * builtin itself; a local binding of the alias's spelling shadows it. */
function builtinCall(
  e: ts.Expression,
  scope: WalkScope,
): (BuiltinEntry & { args: readonly ts.Expression[] }) | undefined {
  if (!ts.isCallExpression(e)) return undefined;
  const callee = e.expression;
  if (ts.isIdentifier(callee) && !scope.vars.has(callee.text)) {
    const alias = scope.aliases.get(modelKey(refOf(scope, callee.text)));
    if (alias !== undefined && admitsArity(alias.arity, e.arguments.length)) {
      return { ...alias, args: e.arguments };
    }
  }
  const spelled = builtinSpelling(callee, bodyBinds(scope));
  if (spelled === undefined) return undefined;
  const entry = BUILTIN_MEMBER_CALLS.get(spelled);
  if (entry === undefined || !admitsArity(entry.arity, e.arguments.length)) {
    return undefined;
  }
  return { ...entry, args: e.arguments };
}

/** A binder's emitted domain: a finite half-open range, the whole int
 * line, the naturals, the two booleans, or a bounded `number` — reading
 * the domain the binder *denotes*, so equivalent spellings of one
 * interval fold to the same shape. `bare` covers everything this slice
 * cannot express; a safe-integer clamp reports its offending endpoints
 * instead, for the unsupported-range refusal. */
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
  // A boolean binder is bare of guards by grammar; its domain is the two
  // values, which the witness search enumerates.
  if (b.domain === "boolean") return { name: b.varName, kind: "boolean" };
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
  return shape.ctorParams.map((slot, i) => {
    const name = shape.ctorParamNames[i]!;
    if (slot === "num") return { name, kind: "number" };
    if (slot === "bool") return { name, kind: "boolean" };
    // A constructor admits no declared union, so a union slot is exactly
    // a defaulted number or boolean, told apart by the tag beside
    // `undefined`; an option slot is a defaulted class.
    if ("union" in slot)
      return slot.union.includes("boolean")
        ? { name, kind: "boolean", defaulted: true }
        : { name, kind: "number", defaulted: true };
    const ref = "option" in slot ? slot.option : slot.instance;
    const inner = classes.get(modelKey(ref))!;
    return {
      name,
      kind: "class",
      className: ref.name,
      ...(ref.module !== "" ? { module: ref.module } : {}),
      ctorParams: lowerCtorParams(inner, classes),
      ...("option" in slot ? { defaulted: true } : {}),
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
 * the model refuses (an opaque construct, an unsupported operator, a
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
      // parameter's do; a boolean binder enters at boolean; every other
      // binder is a number.
      vars: new Map(
        loweredBinders.map((b): [string, ValueTy] => [
          b.name,
          b.kind === "class"
            ? { instance: { module: b.module ?? module, name: b.className } }
            : b.kind === "boolean"
              ? "bool"
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
    // Guards precede the conclusion in the pre-scan roots, so a refusal in
    // a guard is reported before one in the conclusion. The conclusion is
    // pre-scanned as written — an equation splits into its sides only for
    // the typed walk, which lifts them separately.
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

/** The initializer a module-scope declarator pins, when the model admits
 * it: a `const` with an identifier name, no type annotation other than
 * `number`, and a constant expression as initializer. */
function constantInit(
  d: ts.VariableDeclaration,
  admitted: (name: string) => ModelRef | undefined,
  binds: (name: string) => boolean,
): EmitExpr | undefined {
  if (!ts.isIdentifier(d.name)) return undefined;
  if (d.type !== undefined && d.type.kind !== ts.SyntaxKind.NumberKeyword)
    return undefined;
  /* v8 ignore next -- an uninitialized `const` does not typecheck, and the
     run is gated on the project typechecking; `declare` is not admissible. */
  if (d.initializer === undefined) return undefined;
  return constantExpr(d.initializer, admitted, binds);
}

/** A constant expression: numeric literals, the `NaN`/`Infinity` atoms,
 * reads of constants already admitted, and the whitelisted builtin
 * constants, under the arithmetic operators, unary sign, and whitelisted
 * number-valued builtin calls over such arguments. Source order bounds
 * the reads, so a forward or self reference is simply not yet admitted;
 * the atoms and the builtins are read under the module's own shadowing
 * (`binds`), the rule a body applies with no locals in scope; every other
 * shape declines — a call member met as a value included, which leaves
 * it for the alias registration. */
function constantExpr(
  e: ts.Expression,
  admitted: (name: string) => ModelRef | undefined,
  binds: (name: string) => boolean,
): EmitExpr | undefined {
  const u = unwrapParens(e);
  if (ts.isNumericLiteral(u)) return { kind: "num", lit: numberToken(u) };
  const negated = negatedLiteral(u);
  if (negated !== undefined) {
    return { kind: "num", lit: `-${numberToken(negated)}` };
  }
  if (ts.isIdentifier(u)) {
    const ref = admitted(u.text);
    if (ref !== undefined) {
      return {
        kind: "const-read",
        name: ref.name,
        ...(ref.module !== "" ? { module: ref.module } : {}),
      };
    }
    if (GLOBAL_NUMBER_ATOMS.has(u.text) && !binds(u.text)) {
      return { kind: "num", lit: u.text };
    }
    return undefined;
  }
  if (isUnaryArith(u)) {
    const operand = constantExpr(u.operand, admitted, binds);
    if (operand === undefined) return undefined;
    const op = u.operator === ts.SyntaxKind.MinusToken ? "-" : "+";
    return { kind: "unop", op, operand };
  }
  if (ts.isBinaryExpression(u)) {
    const op = u.operatorToken.getText();
    if (!ARITH_OPERATORS.has(op)) return undefined;
    const left = constantExpr(u.left, admitted, binds);
    const right = constantExpr(u.right, admitted, binds);
    if (left === undefined || right === undefined) return undefined;
    return { kind: "binop", op, left, right };
  }
  if (ts.isCallExpression(u)) {
    const spelled = builtinSpelling(u.expression, binds);
    if (spelled === undefined) return undefined;
    const entry = BUILTIN_MEMBER_CALLS.get(spelled);
    if (
      entry === undefined ||
      entry.ty !== "num" ||
      !admitsArity(entry.arity, u.arguments.length)
    ) {
      return undefined;
    }
    const args: EmitExpr[] = [];
    for (const a of u.arguments) {
      const arg = constantExpr(a, admitted, binds);
      if (arg === undefined) return undefined;
      args.push(arg);
    }
    return {
      kind: "builtin",
      object: entry.object,
      member: entry.member,
      args,
    };
  }
  const spelled = builtinSpelling(u, binds);
  if (spelled === undefined) return undefined;
  const read = BUILTIN_MEMBER_READS.get(spelled);
  if (read === undefined) return undefined;
  return { kind: "builtin-read", object: read.object, member: read.member };
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
  /* v8 ignore next -- as in `constantInit`: the declarator reaching here
     is a `const` a typechecked project admits, so it has an initializer. */
  if (d.initializer === undefined) return undefined;
  const init = unwrapParens(d.initializer);
  if (!ts.isPropertyAccessExpression(init) || !ts.isIdentifier(init.expression))
    return undefined;
  const namespace = init.expression.text;
  if (binds(namespace)) return undefined;
  return BUILTIN_MEMBER_CALLS.get(`${namespace}.${init.name.text}`);
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
        // A site is declared before the owner that applies it.
        c.declarations.push(...walked.residuals, walked.emit);
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
        // A site is declared before the owner that applies it.
        c.declarations.push(...walked.residuals, walked.emit);
        c.classes.set(key(className), walked.shape);
        c.mapped.set(
          key(qualifiedName("constructor", className)),
          exactSig(walked.shape.ctorParams),
        );
        for (const [g, returns] of walked.shape.getters) {
          c.mapped.set(key(qualifiedName(g, className)), exactSig([], returns));
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
    // Every other name a declaration binds degrades to an opaque failure,
    // positioned on the binding identifier — except a declarator the
    // constant scan positively admits.
    if (ts.isVariableStatement(stmt)) {
      const admissible =
        (stmt.declarationList.flags & ts.NodeFlags.Const) !== 0 &&
        (ts.getModifiers(stmt) ?? []).every(
          (m) => m.kind === ts.SyntaxKind.ExportKeyword,
        );
      const binds = (name: string) =>
        names.has(name) || c.failed.has(key(name));
      // An initializer's read resolves as a body's does: an import to its
      // exporting module, anything else to this module's own.
      const admitted = (name: string): ModelRef | undefined => {
        const ref = names.get(name) ?? { module: qualifier, name };
        return c.constants.has(modelKey(ref)) ? ref : undefined;
      };
      for (const d of stmt.declarationList.declarations) {
        const init = admissible ? constantInit(d, admitted, binds) : undefined;
        if (init !== undefined) {
          const name = (d.name as ts.Identifier).text;
          c.declarations.push({
            kind: "constant",
            name,
            ...(qualifier !== "" ? { module: qualifier } : {}),
            init,
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
/** Marks every callable whose body reaches a residual site, directly or
 * through a callee that does. Declarations arrive in dependency order — a
 * callee is walked before its caller, a class's constructor before its
 * getters, getters before methods — so one pass sees each callee's flag
 * before the uses that inherit it. */
function markNoncomputable(declarations: readonly EmitDecl[]): void {
  const tainted = new Set<string>();
  const keyOf = (module: string | undefined, name: string) =>
    modelKey({ module: module ?? "", name });
  const memberKeyOf = (
    module: string | undefined,
    cls: string,
    member: string,
  ) => keyOf(module, qualifiedName(member, cls));
  const reaches = (e: EmitExpr): boolean => {
    switch (e.kind) {
      case "residual":
        return true;
      case "call":
        return tainted.has(keyOf(e.module, e.callee)) || e.args.some(reaches);
      case "new":
        return (
          tainted.has(memberKeyOf(e.module, e.className, "constructor")) ||
          e.args.some(reaches)
        );
      case "getter-read":
        return (
          tainted.has(memberKeyOf(e.module, e.className, e.name)) ||
          reaches(e.object)
        );
      case "method-call":
        return (
          tainted.has(memberKeyOf(e.module, e.className, e.name)) ||
          reaches(e.object) ||
          e.args.some(reaches)
        );
      case "field-read":
        return reaches(e.object);
      case "unop":
        return reaches(e.operand);
      case "binop":
      case "same-value":
      case "jsval-eq":
        return reaches(e.left) || reaches(e.right);
      case "cond":
        return reaches(e.cond) || reaches(e.then) || reaches(e.else);
      case "builtin":
        return e.args.some(reaches);
      case "project":
      case "option-test":
      case "option-get":
      case "typeof-test":
        return reaches(e.expr);
      case "inject":
      case "option":
        return e.expr !== undefined && reaches(e.expr);
      // A literal, an identifier, the receiver, and a constant or builtin
      // read reach nothing.
      default:
        return false;
    }
  };
  const bodyReaches = (stmts: readonly EmitStmt[]): boolean =>
    stmts.some((st) => {
      switch (st.kind) {
        case "return":
        case "assign":
        case "field-set":
        case "discard":
          return reaches(st.expr);
        case "const":
        case "let":
          return reaches(st.init);
        case "if":
          return (
            reaches(st.cond) ||
            bodyReaches(st.then) ||
            (st.else !== undefined && bodyReaches(st.else))
          );
        // A throw carries only its error's name.
        default:
          return false;
      }
    });
  for (const d of declarations) {
    if (d.kind === "function") {
      if (bodyReaches(d.body)) {
        d.noncomputable = true;
        tainted.add(keyOf(d.module, d.name));
      }
    } else if (d.kind === "class") {
      if (bodyReaches(d.ctor.body)) {
        d.ctor.noncomputable = true;
        tainted.add(memberKeyOf(d.module, d.name, "constructor"));
      }
      for (const g of d.getters) {
        if (bodyReaches(g.body)) {
          g.noncomputable = true;
          tainted.add(memberKeyOf(d.module, d.name, g.name));
        }
      }
      for (const m of d.methods) {
        if (bodyReaches(m.body)) {
          m.noncomputable = true;
          tainted.add(memberKeyOf(d.module, d.name, m.name));
        }
      }
    }
  }
}

export function emitModule(
  text: string,
  file: string,
  reader: ModuleReader = diskReader,
  refused: ReadonlySet<string> = new Set(),
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
  markNoncomputable(closure.declarations);
  const { declarations, mapped, failed } = closure;
  const module = "";
  const key = (name: string) => modelKey({ module, name });

  const extracted = extractFromSource(text, file);
  // A refused annotation is the CLI's InputError; it is neither an
  // obligation nor a classification here.
  const annotations = extracted.annotations.filter(
    (a) => !refused.has(annotationKey(file, a)),
  );
  const { invalid } = extracted;
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
