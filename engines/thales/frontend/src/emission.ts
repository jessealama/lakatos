import ts from 'typescript';
import {
  type Binder,
  clampedEndpoints,
  extractFromSource,
  intInterval,
  type InvalidAnnotation,
  isClassDomain,
  parseBody,
  parsePrefix,
  qualifiedName,
  type RawAnnotation,
} from '../../../../lemma/src/index.js';
import { kindName, numberToken } from './transcribe.js';

/** A JS expression in the shapes the plain-Lean emitter renders. The
 * frontend records operator text verbatim; what an operator means is the
 * emitter's decision, so the walk here admits exactly the operators the
 * emitter renders and classifies everything else the way the old
 * pipeline's elaborator does. */
export type EmitExpr =
  | { kind: 'num'; lit: string }
  | { kind: 'id'; name: string }
  | { kind: 'unop'; op: '-' | '+'; operand: EmitExpr }
  | { kind: 'binop'; op: string; left: EmitExpr; right: EmitExpr }
  | { kind: 'call'; callee: string; args: EmitExpr[] };

export type EmitStmt = { kind: 'return'; expr: EmitExpr };

export interface EmitFunction {
  kind: 'function';
  name: string;
  /** Parameter names; every parameter is `: number`. */
  params: string[];
  /** The declaration's original text, echoed as comments above the def. */
  source: string;
  body: EmitStmt[];
}

/** A binder's denoted integer domain: a finite half-open range, the whole
 * int line, or the naturals — the same three shapes the old grammar's
 * binder constructors carry. */
export type EmitBinder =
  | { name: string; kind: 'range'; lo: string; hi: string }
  | { name: string; kind: 'int' }
  | { name: string; kind: 'nat' };

export interface EmitObligation {
  /** Qualified function name — the annotation identity's `function`. */
  function: string;
  property: string;
  /** Whitespace-normalized formula, echoed as a comment above the command. */
  formula: string;
  payload:
    | {
        kind: 'structured';
        /** Nested binders, outermost first. */
        binders: EmitBinder[];
        conclusion:
          | { kind: 'eq'; left: EmitExpr; right: EmitExpr }
          | { kind: 'istrue'; expr: EmitExpr };
      }
    | { kind: 'bare' };
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
  szs: 'Inappropriate' | 'Error';
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
    '**',
    "'**' is implementation-approximated in JavaScript, so any model would " +
      'certify results a conforming engine may disagree with',
  ],
]);

const ARITH_OPERATORS = new Set(['+', '-', '*', '/', '%']);
const COMPARISON_OPERATORS = new Set(['<', '<=', '>', '>=', '===', '!==']);

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
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    into.push(e.expression.text);
    for (const a of e.arguments) callNames(a, into);
  }
  return into;
}

/** What a body or formula may reference: bound value names, the models
 * registered so far, and the declarations that failed. */
interface WalkScope {
  vars: ReadonlySet<string>;
  mapped: ReadonlyMap<string, number>;
  failed: ReadonlyMap<string, FailedDecl>;
}

/** The first callee whose own declaration failed on a named construct:
 * the refusal travels with the call. A callee that failed for any other
 * reason is left to the typed walk, as the old elaborator leaves it to
 * `evalExpr`. */
function findFailedCallee(
  e: ts.Expression,
  scope: WalkScope,
): FailedDecl | undefined {
  for (const name of callNames(e)) {
    if (scope.mapped.has(name)) continue;
    const failed = scope.failed.get(name);
    if (failed?.construct !== undefined) {
      return {
        construct: failed.construct,
        reason: `'${name}' could not be modeled: ${failed.reason}`,
      };
    }
  }
  return undefined;
}

type Expected = 'num' | 'bool';

function describeTy(t: Expected): string {
  return t === 'num' ? 'a number' : 'a boolean';
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
    if (expected !== 'num') {
      throw new ModelError(
        `a numeric literal cannot be ${describeTy(expected)}`,
      );
    }
    const lit =
      negated !== undefined
        ? `-${numberToken(negated)}`
        : numberToken(e as ts.NumericLiteral);
    return { kind: 'num', lit };
  }
  if (ts.isIdentifier(e)) {
    if (!scope.vars.has(e.text)) {
      throw new ModelError(`unbound identifier '${e.text}'`);
    }
    if (expected !== 'num') {
      throw new ModelError(
        `identifier '${e.text}' is a number, not ${describeTy(expected)}`,
      );
    }
    return { kind: 'id', name: e.text };
  }
  if (isUnaryArith(e)) {
    const operand = walkTyped(e.operand, 'num', scope, sf);
    const op = e.operator === ts.SyntaxKind.MinusToken ? '-' : '+';
    if (expected !== 'num') {
      throw new ModelError(
        `operator '${op}' yields a number, not ${describeTy(expected)}`,
      );
    }
    return { kind: 'unop', op, operand };
  }
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText(sf);
    const left = walkTyped(e.left, 'num', scope, sf);
    const right = walkTyped(e.right, 'num', scope, sf);
    if (ARITH_OPERATORS.has(op)) {
      if (expected !== 'num') {
        throw new ModelError(
          `operator '${op}' yields a number, not ${describeTy(expected)}`,
        );
      }
      return { kind: 'binop', op, left, right };
    }
    if (COMPARISON_OPERATORS.has(op)) {
      if (expected !== 'bool') {
        throw new ModelError(
          `operator '${op}' yields a boolean, not ${describeTy(expected)}`,
        );
      }
      return { kind: 'binop', op, left, right };
    }
    // A refused operator the pre-scans missed still refuses; anything
    // else has no model, which is the engine's problem.
    const refused = REFUSED_OPERATORS.get(op);
    if (refused !== undefined) throw new ModelError(refused);
    throw new ModelError(`operator '${op}' has no model in this slice`);
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    const name = e.expression.text;
    const arity = scope.mapped.get(name);
    if (arity === undefined) {
      const failed = scope.failed.get(name);
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
    if (expected !== 'num') {
      throw new ModelError(
        `a call to '${name}' yields a number, not ${describeTy(expected)}`,
      );
    }
    const args = e.arguments.map((a) => walkTyped(a, 'num', scope, sf));
    return { kind: 'call', callee: name, args };
  }
  // Unreachable after the construct scan; degrade like an opaque node.
  throw new ModelError(constructAt(e, e.kind, sf).reason);
}

/** An expression's IR or its failure, checked in the old elaborator's
 * order: opaque constructs, then refused operators, then construct-failed
 * callees, then the typed walk. */
function walkChecked(
  e: ts.Expression,
  expected: Expected,
  scope: WalkScope,
  sf: ts.SourceFile,
): { expr: EmitExpr } | FailedDecl {
  const failure =
    findConstruct(e, sf) ?? findRefusedOp(e) ?? findFailedCallee(e, scope);
  if (failure !== undefined) return failure;
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

/** A function declaration's IR, or its failure. This slice covers exactly
 * a body of `return <expr>` statements — statement breadth is a later
 * slice, and anything beyond it must degrade, not approximate. */
function walkFunction(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
  mapped: ReadonlyMap<string, number>,
  failed: ReadonlyMap<string, FailedDecl>,
): EmitFunction | FailedDecl {
  const sig = signatureFailure(fn, sf);
  if (sig !== undefined) return sig;
  const params = fn.parameters.map((p) => (p.name as ts.Identifier).text);
  const scope: WalkScope = { vars: new Set(params), mapped, failed };
  const body: EmitStmt[] = [];
  for (const s of fn.body!.statements) {
    if (!ts.isReturnStatement(s) || s.expression === undefined) {
      return constructAt(s, s.kind, sf);
    }
    const walked = walkChecked(s.expression, 'num', scope, sf);
    if (!('expr' in walked)) return walked;
    body.push({ kind: 'return', expr: walked.expr });
  }
  return {
    kind: 'function',
    name: fn.name!.text,
    params,
    source: fn.getText(sf),
    body,
  };
}

/** Parse one formula atom the way the transcriber does: wrapped in
 * parentheses, rejected on any parser diagnostic. */
function parseAtomExpr(
  js: string,
): { sf: ts.SourceFile; expr: ts.Expression } | undefined {
  const sf = ts.createSourceFile(
    'atom.ts',
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
    callee.expression.text !== 'Object' ||
    callee.name.text !== 'is'
  ) {
    return undefined;
  }
  return [e.arguments[0]!, e.arguments[1]!];
}

/** A binder's emitted domain: a finite half-open range, the whole int
 * line, or the naturals — reading the domain the binder *denotes*, the
 * same folding the old transcriber applies. `bare` covers everything this
 * slice cannot express. */
function lowerBinder(b: Binder): EmitBinder | 'bare' {
  if (b.domain !== 'int' && b.domain !== 'nat') return 'bare';
  if (b.range === undefined) {
    return { name: b.varName, kind: b.domain === 'nat' ? 'nat' : 'int' };
  }
  const { lo, hi } = intInterval(b.domain, b.range);
  if (hi === undefined) {
    if (lo === undefined) return { name: b.varName, kind: 'int' };
    return lo === 0n ? { name: b.varName, kind: 'nat' } : 'bare';
  }
  if (lo === undefined) return 'bare';
  if (clampedEndpoints(b).length > 0) return 'bare';
  return {
    name: b.varName,
    kind: 'range',
    lo: lo.toString(),
    hi: (hi + 1n).toString(),
  };
}

type PayloadResult =
  | { kind: 'payload'; payload: EmitObligation['payload'] }
  | { kind: 'classified'; szs: 'Inappropriate' | 'Error'; reason: string };

/** The structured reading of an annotation formula: int/nat binders and a
 * single conclusion atom — guards and every other connective wait for
 * their slices and degrade to bare. A formula the model refuses (an
 * opaque construct, a refused operator, a construct-failed callee)
 * classifies `Inappropriate` with the old pipeline's reason; one the
 * typed walk fails classifies `Error` the way a failed property
 * elaboration does. */
function obligationPayload(
  formula: string,
  mapped: ReadonlyMap<string, number>,
  failed: ReadonlyMap<string, FailedDecl>,
): PayloadResult {
  const bare: PayloadResult = { kind: 'payload', payload: { kind: 'bare' } };
  try {
    const { binders, body } = parsePrefix(formula);
    const loweredBinders: EmitBinder[] = [];
    for (const b of binders) {
      const lowered = lowerBinder(b);
      if (lowered === 'bare') return bare;
      loweredBinders.push(lowered);
    }
    const ast = parseBody(body);
    if (ast.kind !== 'atom') return bare;
    const parsed = parseAtomExpr(ast.js);
    if (parsed === undefined) return bare;
    const expr = unwrapParens(parsed.expr);
    const sides = equationSides(expr);
    const scope: WalkScope = {
      vars: new Set(binders.map((b) => b.varName)),
      mapped,
      failed,
    };
    const roots: [ts.Expression, Expected][] =
      sides !== undefined
        ? [
            [sides[0], 'num'],
            [sides[1], 'num'],
          ]
        : [[expr, 'bool']];
    // The old elaborator's pre-scan order over the whole property: opaque
    // constructs, then refused operators, then construct-failed callees —
    // each scan across the full tree before the next begins.
    for (const [root] of roots) {
      const construct = findConstruct(root, parsed.sf);
      if (construct !== undefined) {
        return {
          kind: 'classified',
          szs: 'Inappropriate',
          reason: construct.reason,
        };
      }
    }
    for (const [root] of roots) {
      const refused = findRefusedOp(root);
      if (refused !== undefined) {
        return {
          kind: 'classified',
          szs: 'Inappropriate',
          reason: refused.reason,
        };
      }
    }
    for (const [root] of roots) {
      const callee = findFailedCallee(root, scope);
      if (callee !== undefined) {
        return {
          kind: 'classified',
          szs: 'Inappropriate',
          reason: callee.reason,
        };
      }
    }
    try {
      if (sides !== undefined) {
        const left = walkTyped(sides[0], 'num', scope, parsed.sf);
        const right = walkTyped(sides[1], 'num', scope, parsed.sf);
        return {
          kind: 'payload',
          payload: {
            kind: 'structured',
            binders: loweredBinders,
            conclusion: { kind: 'eq', left, right },
          },
        };
      }
      const walked = walkTyped(expr, 'bool', scope, parsed.sf);
      return {
        kind: 'payload',
        payload: {
          kind: 'structured',
          binders: loweredBinders,
          conclusion: { kind: 'istrue', expr: walked },
        },
      };
    } catch (err) {
      if (err instanceof ModelError) {
        return {
          kind: 'classified',
          szs: 'Error',
          reason: `property elaboration failed: ${err.message}`,
        };
      }
      throw err;
    }
  } catch {
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

/**
 * Walk one module into the plain-Lean emission IR: mappable function
 * declarations with their bodies, one obligation per annotation on a
 * mapped function, and a frontend classification — with the old
 * pipeline's exact status and reason — for each annotation the model
 * refuses or the engine cannot attempt. Import closures are a later
 * slice; an import degrades like any other unmapped declaration.
 */
export function emitModule(text: string, file: string): PlainEmission {
  const sf = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true);
  const declarations: EmitFunction[] = [];
  const mapped = new Map<string, number>();
  const failed = new Map<string, FailedDecl>();
  for (const stmt of sf.statements) {
    if (ts.isFunctionDeclaration(stmt)) {
      if (stmt.name === undefined) continue;
      const walked = walkFunction(stmt, sf, mapped, failed);
      if ('kind' in walked && walked.kind === 'function') {
        declarations.push(walked);
        mapped.set(stmt.name.text, walked.params.length);
      } else {
        failed.set(stmt.name.text, walked as FailedDecl);
      }
      continue;
    }
    if (ts.isClassDeclaration(stmt)) {
      if (stmt.name === undefined) continue;
      const className = stmt.name.text;
      failed.set(className, constructAt(stmt.name, stmt.kind, sf));
      for (const member of stmt.members) {
        const name = member.name;
        if (name === undefined || !ts.isIdentifier(name)) continue;
        const isStatic = (
          ts.getModifiers(member as ts.HasModifiers) ?? []
        ).some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
        failed.set(
          qualifiedName(name.text, className, isStatic),
          constructAt(name, stmt.kind, sf),
        );
      }
      continue;
    }
    // Any other named declaration binds outside the model.
    const name = (stmt as { name?: ts.Node }).name;
    if (name !== undefined && ts.isIdentifier(name)) {
      failed.set(name.text, constructAt(name, stmt.kind, sf));
    }
  }

  const { annotations, invalid } = extractFromSource(text, file);
  const obligations: EmitObligation[] = [];
  const classified: ClassifiedAnnotation[] = [];
  for (const a of annotations) {
    const fn = qualifiedName(a.functionName, a.className, a.isStatic);
    const classBinder = classBinderReason(a.formula);
    if (classBinder !== undefined) {
      classified.push({
        annotation: a,
        szs: 'Inappropriate',
        reason: classBinder,
      });
      continue;
    }
    const fnFailed = failed.get(fn);
    if (fnFailed !== undefined) {
      classified.push({
        annotation: a,
        szs: fnFailed.construct !== undefined ? 'Inappropriate' : 'Error',
        reason: `'${fn}' could not be modeled: ${fnFailed.reason}`,
      });
      continue;
    }
    const result = obligationPayload(a.formula, mapped, failed);
    if (result.kind === 'classified') {
      classified.push({
        annotation: a,
        szs: result.szs,
        reason: result.reason,
      });
      continue;
    }
    obligations.push({
      function: fn,
      property: a.propertyName,
      formula: a.formula.replace(/\s+/g, ' ').trim(),
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
