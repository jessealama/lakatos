import ts from 'typescript';
import {
  clampedEndpoints,
  extractFromSource,
  intInterval,
  type InvalidAnnotation,
  parseBody,
  parsePrefix,
  qualifiedName,
  type RawAnnotation,
} from '../../../../lemma/src/index.js';
import { kindName, numberToken } from './transcribe.js';

/** A JS expression in the shapes the plain-Lean emitter renders. The
 * frontend records operator text verbatim; what an operator means is the
 * emitter's decision, so an op this slice cannot render fails there,
 * cleanly, rather than being silently reshaped here. */
export type EmitExpr =
  | { kind: 'num'; lit: string }
  | { kind: 'id'; name: string }
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

export interface EmitObligation {
  /** Qualified function name — the annotation identity's `function`. */
  function: string;
  property: string;
  /** Whitespace-normalized formula, echoed as a comment above the command. */
  formula: string;
  payload:
    | {
        kind: 'structured';
        /** Nested half-open [lo, hi) Int binders, outermost first. */
        binders: { name: string; lo: string; hi: string }[];
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

/** An annotation the frontend itself refuses: its function could not be
 * mapped, and the named construct makes that a statement about the input.
 * The reason is byte-identical to the old pipeline's, which is what the
 * parity harness pins. */
export interface ClassifiedAnnotation {
  annotation: RawAnnotation;
  szs: 'Inappropriate';
  reason: string;
}

export interface PlainEmission {
  emission: Emission;
  annotations: RawAnnotation[];
  invalid: InvalidAnnotation[];
  classified: ClassifiedAnnotation[];
}

/** The construct that keeps a declaration outside the model, at its
 * 1-based source position. */
interface Blocker {
  construct: string;
  line: number;
  column: number;
}

function blockerAt(
  node: ts.Node,
  kind: ts.SyntaxKind,
  sf: ts.SourceFile,
): Blocker {
  const { line, character } = sf.getLineAndCharacterOfPosition(
    node.getStart(sf),
  );
  return { construct: kindName(kind), line: line + 1, column: character + 1 };
}

/** The operators whose result the emitter has a rendering for. Meaning
 * still lives Lean-side; this set only bounds what travels as `binop`. */
const EMITTABLE_OPERATORS = new Set([
  '+',
  '-',
  '*',
  '/',
  '%',
  '<',
  '<=',
  '>',
  '>=',
  '===',
  '!==',
]);

function unwrapParens(e: ts.Expression): ts.Expression {
  return ts.isParenthesizedExpression(e) ? unwrapParens(e.expression) : e;
}

/** An expression's IR, or the first blocker in tree order. */
function walkExpr(e: ts.Expression, sf: ts.SourceFile): EmitExpr | Blocker {
  if (ts.isParenthesizedExpression(e)) return walkExpr(e.expression, sf);
  if (ts.isIdentifier(e)) return { kind: 'id', name: e.text };
  if (ts.isNumericLiteral(e)) return { kind: 'num', lit: numberToken(e) };
  if (
    ts.isPrefixUnaryExpression(e) &&
    e.operator === ts.SyntaxKind.MinusToken &&
    ts.isNumericLiteral(e.operand)
  ) {
    return { kind: 'num', lit: `-${numberToken(e.operand)}` };
  }
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText(sf);
    if (!EMITTABLE_OPERATORS.has(op)) return blockerAt(e, e.kind, sf);
    const left = walkExpr(e.left, sf);
    if ('construct' in left) return left;
    const right = walkExpr(e.right, sf);
    if ('construct' in right) return right;
    return { kind: 'binop', op, left, right };
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    const args: EmitExpr[] = [];
    for (const a of e.arguments) {
      const walked = walkExpr(a, sf);
      if ('construct' in walked) return walked;
      args.push(walked);
    }
    return { kind: 'call', callee: e.expression.text, args };
  }
  return blockerAt(e, e.kind, sf);
}

/** The signature check `transcribeFunction` applies, as a blocker. */
function signatureBlocker(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
): Blocker | undefined {
  for (const m of fn.modifiers ?? []) {
    if (
      m.kind !== ts.SyntaxKind.ExportKeyword &&
      m.kind !== ts.SyntaxKind.DefaultKeyword
    ) {
      return blockerAt(m, m.kind, sf);
    }
  }
  if (fn.asteriskToken !== undefined)
    return blockerAt(fn.asteriskToken, fn.asteriskToken.kind, sf);
  for (const p of fn.parameters) {
    if (!ts.isIdentifier(p.name)) return blockerAt(p.name, p.name.kind, sf);
    if (p.dotDotDotToken !== undefined)
      return blockerAt(p.dotDotDotToken, p.dotDotDotToken.kind, sf);
    if (p.questionToken !== undefined || p.initializer !== undefined)
      return blockerAt(p, p.kind, sf);
    if (p.type === undefined) return blockerAt(p, p.kind, sf);
    if (p.type.kind !== ts.SyntaxKind.NumberKeyword)
      return blockerAt(p.type, p.type.kind, sf);
  }
  if (fn.type === undefined || fn.body === undefined)
    return blockerAt(fn, fn.kind, sf);
  if (fn.type.kind !== ts.SyntaxKind.NumberKeyword)
    return blockerAt(fn.type, fn.type.kind, sf);
  return undefined;
}

/** A function declaration's IR, or its first blocker. This slice covers
 * exactly a body of `return <expr>` statements — statement breadth is a
 * later slice, and anything beyond it must degrade, not approximate. */
function walkFunction(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
): EmitFunction | Blocker {
  const sig = signatureBlocker(fn, sf);
  if (sig !== undefined) return sig;
  const body: EmitStmt[] = [];
  for (const s of fn.body!.statements) {
    if (!ts.isReturnStatement(s) || s.expression === undefined) {
      return blockerAt(s, s.kind, sf);
    }
    const expr = walkExpr(s.expression, sf);
    if ('construct' in expr) return expr;
    body.push({ kind: 'return', expr });
  }
  return {
    kind: 'function',
    name: fn.name!.text,
    params: fn.parameters.map((p) => (p.name as ts.Identifier).text),
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

/** The structured reading of an annotation formula, or bare when this
 * slice cannot express it: only all-int/nat binders whose denoted domain
 * is a finite unclamped [lo, hi), and a single conclusion atom — guards
 * and every other connective wait for their slices. */
function obligationPayload(formula: string): EmitObligation['payload'] {
  const bare = { kind: 'bare' as const };
  try {
    const { binders, body } = parsePrefix(formula);
    const loweredBinders: { name: string; lo: string; hi: string }[] = [];
    for (const b of binders) {
      if (b.domain !== 'int' && b.domain !== 'nat') return bare;
      if (b.range === undefined) return bare;
      const { lo, hi } = intInterval(b.domain, b.range);
      if (lo === undefined || hi === undefined) return bare;
      if (clampedEndpoints(b).length > 0) return bare;
      loweredBinders.push({
        name: b.varName,
        lo: lo.toString(),
        hi: (hi + 1n).toString(),
      });
    }
    const ast = parseBody(body);
    if (ast.kind !== 'atom') return bare;
    const parsed = parseAtomExpr(ast.js);
    if (parsed === undefined) return bare;
    const expr = unwrapParens(parsed.expr);
    const sides = equationSides(expr);
    if (sides !== undefined) {
      const left = walkExpr(sides[0], parsed.sf);
      if ('construct' in left) return bare;
      const right = walkExpr(sides[1], parsed.sf);
      if ('construct' in right) return bare;
      return {
        kind: 'structured',
        binders: loweredBinders,
        conclusion: { kind: 'eq', left, right },
      };
    }
    const walked = walkExpr(expr, parsed.sf);
    if ('construct' in walked) return bare;
    return {
      kind: 'structured',
      binders: loweredBinders,
      conclusion: { kind: 'istrue', expr: walked },
    };
  } catch {
    return bare;
  }
}

/**
 * Walk one module into the plain-Lean emission IR: mappable function
 * declarations with their bodies, one obligation per annotation on a
 * mapped function, and a frontend `Inappropriate` classification — with
 * the old pipeline's exact reason string — for each annotation whose
 * function could not be mapped. Import closures are a later slice; an
 * import degrades like any other unmapped declaration.
 */
export function emitModule(text: string, file: string): PlainEmission {
  const sf = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true);
  const declarations: EmitFunction[] = [];
  const blockers = new Map<string, Blocker>();
  for (const stmt of sf.statements) {
    if (ts.isFunctionDeclaration(stmt)) {
      if (stmt.name === undefined) continue;
      const walked = walkFunction(stmt, sf);
      if ('construct' in walked) blockers.set(stmt.name.text, walked);
      else declarations.push(walked);
      continue;
    }
    if (ts.isClassDeclaration(stmt)) {
      if (stmt.name === undefined) continue;
      const className = stmt.name.text;
      blockers.set(className, blockerAt(stmt.name, stmt.kind, sf));
      for (const member of stmt.members) {
        const name = member.name;
        if (name === undefined || !ts.isIdentifier(name)) continue;
        const isStatic = (
          ts.getModifiers(member as ts.HasModifiers) ?? []
        ).some((m) => m.kind === ts.SyntaxKind.StaticKeyword);
        blockers.set(
          qualifiedName(name.text, className, isStatic),
          blockerAt(name, stmt.kind, sf),
        );
      }
      continue;
    }
    // Any other named declaration binds outside the model.
    const name = (stmt as { name?: ts.Node }).name;
    if (name !== undefined && ts.isIdentifier(name)) {
      blockers.set(name.text, blockerAt(name, stmt.kind, sf));
    }
  }

  const { annotations, invalid } = extractFromSource(text, file);
  const obligations: EmitObligation[] = [];
  const classified: ClassifiedAnnotation[] = [];
  for (const a of annotations) {
    const fn = qualifiedName(a.functionName, a.className, a.isStatic);
    const blocker = blockers.get(fn);
    if (blocker !== undefined) {
      classified.push({
        annotation: a,
        szs: 'Inappropriate',
        reason:
          `'${fn}' could not be modeled: unmapped TypeScript construct ` +
          `'${blocker.construct}' at ${blocker.line}:${blocker.column}`,
      });
      continue;
    }
    obligations.push({
      function: fn,
      property: a.propertyName,
      formula: a.formula.replace(/\s+/g, ' ').trim(),
      payload: obligationPayload(a.formula),
    });
  }
  return {
    emission: { file, declarations, obligations },
    annotations,
    invalid,
    classified,
  };
}
