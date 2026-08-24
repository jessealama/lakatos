import * as fs from 'node:fs';
import ts from 'typescript';
import {
  type Binder,
  clampedEndpoints,
  EmptyAfterClampError,
  extractFromSource,
  intInterval,
  type Formula,
  type InvalidAnnotation,
  parseBody,
  parsePrefix,
  qualifiedName,
  type RawAnnotation,
  unsupportedRangeReason,
} from '../../../../lemma/src/index.js';

/** Escape a string for a Lean string literal. */
function leanStr(s: string): string {
  return JSON.stringify(s);
}

/** 1-based `line, column` of a node's start, as constructor arguments. */
function positionArgs(node: ts.Node, sf: ts.SourceFile): string {
  const { line, character } = sf.getLineAndCharacterOfPosition(
    node.getStart(sf),
  );
  return `${line + 1}, ${character + 1}`;
}

/** The proper name of each SyntaxKind: plain reverse lookup can land on a
 * First-/Last- range marker sharing the same value, so pick the first
 * non-marker name per value. Every kind has one. */
const KIND_NAMES = new Map<number, string>();
for (const [name, value] of Object.entries(ts.SyntaxKind)) {
  if (
    typeof value === 'number' &&
    !/^(First|Last)[A-Z]/.test(name) &&
    !KIND_NAMES.has(value)
  ) {
    KIND_NAMES.set(value, name);
  }
}

function kindName(kind: ts.SyntaxKind): string {
  return KIND_NAMES.get(kind)!;
}

/** An opaque node for `node`, carrying its SyntaxKind name and 1-based
 * line:column in the original source. */
function opaque(node: ts.Node, sf: ts.SourceFile): string {
  return `ts.opaque[${leanStr(kindName(node.kind))}](${positionArgs(node, sf)})`;
}

/** An opaque ts_def: `name` came from a construct of `kind` located at
 * `at`, which the transcriber does not model. */
function opaqueDef(
  name: string,
  kind: ts.SyntaxKind,
  at: ts.Node,
  sf: ts.SourceFile,
): string {
  return (
    `ts_def ${leanStr(name)} := ` +
    `ts.opaque[${leanStr(kindName(kind))}](${positionArgs(at, sf)})`
  );
}

/** The integer value of a numeric literal, or undefined for non-integers. */
function integerValue(lit: ts.NumericLiteral): bigint | undefined {
  const n = Number(lit.text);
  if (!Number.isSafeInteger(n)) return undefined;
  return BigInt(n);
}

function transcribeExpr(e: ts.Expression, sf: ts.SourceFile): string {
  if (ts.isIdentifier(e)) return `ts.id[${leanStr(e.text)}]`;
  if (ts.isNumericLiteral(e)) {
    const v = integerValue(e);
    if (v !== undefined) return `ts.num[${v}]`;
  }
  if (
    ts.isPrefixUnaryExpression(e) &&
    e.operator === ts.SyntaxKind.MinusToken &&
    ts.isNumericLiteral(e.operand)
  ) {
    const v = integerValue(e.operand);
    if (v !== undefined) return `ts.num[-${v}]`;
  }
  if (ts.isParenthesizedExpression(e)) return transcribeExpr(e.expression, sf);
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText(sf);
    const l = transcribeExpr(e.left, sf);
    const r = transcribeExpr(e.right, sf);
    return `ts.binop[${leanStr(op)}](${l}, ${r})`;
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    const args = e.arguments.map((a) => transcribeExpr(a, sf));
    return `ts.call[${leanStr(e.expression.text)}](${args.join(', ')})`;
  }
  return opaque(e, sf);
}

/** `ts.const` lines for a const statement's declarators, or undefined
 * when any declarator falls outside the slice. `await using` shares the
 * Const flag, so the Using bit is excluded explicitly. */
function constLines(
  s: ts.VariableStatement,
  sf: ts.SourceFile,
): string[] | undefined {
  const flags = s.declarationList.flags;
  if ((flags & ts.NodeFlags.Const) === 0) return undefined;
  if ((flags & ts.NodeFlags.Using) !== 0) return undefined;
  // Parser recovery can yield a declarator list with no declarators.
  if (s.declarationList.declarations.length === 0) return undefined;
  const lines: string[] = [];
  for (const d of s.declarationList.declarations) {
    if (!ts.isIdentifier(d.name)) return undefined;
    if (d.initializer === undefined) return undefined;
    if (d.type !== undefined && d.type.kind !== ts.SyntaxKind.NumberKeyword)
      return undefined;
    lines.push(
      `ts.const[${leanStr(d.name.text)}](${transcribeExpr(d.initializer, sf)})`,
    );
  }
  return lines;
}

function transcribeStmt(s: ts.Statement, sf: ts.SourceFile): string[] {
  if (ts.isReturnStatement(s) && s.expression !== undefined) {
    return [`ts.return(${transcribeExpr(s.expression, sf)})`];
  }
  if (ts.isVariableStatement(s)) {
    const lines = constLines(s, sf);
    if (lines !== undefined) return lines;
  }
  return [opaque(s, sf)];
}

/** The node that keeps a function declaration's signature outside the
 * grammar (which can only say `ident: number` parameters and a `number`
 * return), or undefined when the signature is fully expressible. */
function signatureBlocker(fn: ts.FunctionDeclaration): ts.Node | undefined {
  for (const m of fn.modifiers ?? []) {
    if (
      m.kind !== ts.SyntaxKind.ExportKeyword &&
      m.kind !== ts.SyntaxKind.DefaultKeyword
    ) {
      return m;
    }
  }
  if (fn.asteriskToken !== undefined) return fn.asteriskToken;
  for (const p of fn.parameters) {
    if (!ts.isIdentifier(p.name)) return p.name;
    if (p.dotDotDotToken !== undefined) return p.dotDotDotToken;
    if (p.questionToken !== undefined || p.initializer !== undefined) return p;
    if (p.type === undefined) return p;
    if (p.type.kind !== ts.SyntaxKind.NumberKeyword) return p.type;
  }
  if (fn.type === undefined || fn.body === undefined) return fn;
  if (fn.type.kind !== ts.SyntaxKind.NumberKeyword) return fn.type;
  return undefined;
}

function transcribeFunction(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
): string[] {
  if (fn.name === undefined) return [];
  const blocker = signatureBlocker(fn);
  if (blocker !== undefined) {
    return [opaqueDef(fn.name.text, blocker.kind, blocker, sf)];
  }
  const params = fn.parameters.map(
    (p) => `ts.param[${leanStr((p.name as ts.Identifier).text)}](ts.number)`,
  );
  const body = (fn.body?.statements ?? []).flatMap((s) =>
    transcribeStmt(s, sf).map((line) => `  ${line}`),
  );
  return [
    `ts_def ${leanStr(fn.name.text)} := ts.fn(${params.join(', ')}) : ts.number {`,
    ...body,
    '}',
  ];
}

/** Every identifier bound by a binding name (destructuring included). */
function bindingIdentifiers(name: ts.BindingName): ts.Identifier[] {
  if (ts.isIdentifier(name)) return [name];
  const found: ts.Identifier[] = [];
  for (const el of name.elements) {
    if (ts.isBindingElement(el)) found.push(...bindingIdentifiers(el.name));
  }
  return found;
}

/** Opaque ts_defs for every name a non-function declaration binds. */
function transcribeOtherDecl(stmt: ts.Statement, sf: ts.SourceFile): string[] {
  const def = (name: string, at: ts.Node) => opaqueDef(name, stmt.kind, at, sf);
  if (ts.isVariableStatement(stmt)) {
    return stmt.declarationList.declarations.flatMap((d) =>
      bindingIdentifiers(d.name).map((id) => def(id.text, id)),
    );
  }
  if (ts.isClassDeclaration(stmt)) {
    if (stmt.name === undefined) return [];
    const className = stmt.name.text;
    const defs = [def(className, stmt.name)];
    for (const member of stmt.members) {
      const name = member.name;
      if (name === undefined || !ts.isIdentifier(name)) continue;
      const isStatic = (ts.getModifiers(member as ts.HasModifiers) ?? []).some(
        (m) => m.kind === ts.SyntaxKind.StaticKeyword,
      );
      defs.push(def(qualifiedName(name.text, className, isStatic), name));
    }
    return defs;
  }
  if (ts.isImportDeclaration(stmt)) {
    const clause = stmt.importClause;
    if (clause === undefined) return [];
    const defs: string[] = [];
    if (clause.name !== undefined)
      defs.push(def(clause.name.text, clause.name));
    const bindings = clause.namedBindings;
    if (bindings !== undefined) {
      if (ts.isNamespaceImport(bindings)) {
        defs.push(def(bindings.name.text, bindings.name));
      } else {
        for (const el of bindings.elements)
          defs.push(def(el.name.text, el.name));
      }
    }
    return defs;
  }
  // Any other named declaration (enum, interface, type alias, namespace).
  const name = (stmt as { name?: ts.Node }).name;
  if (name !== undefined && ts.isIdentifier(name))
    return [def(name.text, name)];
  return [];
}

type BinderLowering =
  /** The bounded ∀-binder constructor for this binder. */
  | { kind: 'ctor'; ctor: string }
  /** The range only fits after the safe-integer clamp; proving over the
   * clamped domain would be a narrower statement than the user wrote.
   * Carries the offending endpoint literals as the user wrote them. */
  | { kind: 'clamped'; endpoints: string[] }
  /** No `ts.range` reading at all (non-integer domain, unbounded side). */
  | { kind: 'bare' };

/** The comparison a `number` bound lowers to. An interval excludes an endpoint
 * by adjacency in an ordering where -0 sits below 0, which IEEE comparison
 * cannot express: a strict bound at the zero the interval still admits would
 * drop it. Relaxing just those two spellings keeps the prover's domain a
 * superset of the refuter's, which is the safe direction to diverge in. */
function numberBoundOp(
  endpoint: string,
  side: 'lower' | 'upper',
  open: boolean | undefined,
): '<' | '<=' {
  if (!open) return '<=';
  const v = Number(endpoint);
  // Object.is separates the zeros where === does not.
  const relax = side === 'lower' ? Object.is(v, -0) : Object.is(v, 0);
  return relax ? '<=' : '<';
}

/** One side of the guard a `number` binder lowers to. */
export interface GuardBound {
  op: '<' | '<=';
  /** The endpoint as a double, on the side the comparison reads it:
   * `lo.op` compares `lo.val` against the bound variable, `hi.op` the
   * variable against `hi.val`. */
  val: number;
  /** The endpoint as the DSL literal the emitted bound carries. */
  lit: string;
}

/** The guard a `number` binder's interval lowers to, as comparisons rather
 * than as DSL text. An interval guards both of its sides: an ∞ endpoint
 * bounds against the literal infinity — strictly when open, so that sign's
 * infinity is excluded, non-strictly when closed, which IEEE comparison
 * still refuses for NaN. That makes any interval NaN-free, matching the
 * refuter's unconditional noNaN, and reporting the guard this way is what
 * lets a test pin the two engines' domains against each other. Only a
 * binder with no interval at all is unguarded. */
export function numberGuard(range: Binder['range']): {
  lo?: GuardBound;
  hi?: GuardBound;
} {
  if (range === undefined) return {};
  const lo =
    range.min !== undefined
      ? {
          op: numberBoundOp(range.min, 'lower', range.minOpen),
          val: Number(range.min),
          lit: range.min,
        }
      : {
          op: range.minOpen ? ('<' as const) : ('<=' as const),
          val: Number.NEGATIVE_INFINITY,
          lit: '-Infinity',
        };
  const hi =
    range.max !== undefined
      ? {
          op: numberBoundOp(range.max, 'upper', range.maxOpen),
          val: Number(range.max),
          lit: range.max,
        }
      : {
          op: range.maxOpen ? ('<' as const) : ('<=' as const),
          val: Number.POSITIVE_INFINITY,
          lit: 'Infinity',
        };
  return { lo, hi };
}

/** The `ballIco`-style lowering of a binder: inclusive lo, exclusive hi.
 * Lowering reads the domain the binder *denotes*, so `int ∈ [0, ∞)` and
 * `nat` — or `nat ∈ (-∞, 10]` and `nat ∈ [0, 10]` — cannot diverge. */
function binderConstructor(b: Binder): BinderLowering {
  if (b.domain === 'number') {
    // A number interval's openness cannot be normalized away the way an
    // integer one's can, so each side keeps its own comparison; an absent
    // endpoint bounds against the literal infinity, and only an absent
    // interval is unguarded. The comparisons come from numberGuard so that
    // what is emitted and what is checked cannot drift.
    const guard = numberGuard(b.range);
    const bounds: string[] = [];
    if (guard.lo)
      bounds.push(
        `ts.lower[${leanStr(guard.lo.op)}](ts.fnum[${guard.lo.lit}])`,
      );
    if (guard.hi)
      bounds.push(
        `ts.upper[${leanStr(guard.hi.op)}](ts.fnum[${guard.hi.lit}])`,
      );
    // No safe-integer clamp here: a number binder denotes binary64 values
    // directly, so there is no representability question to answer.
    return {
      kind: 'ctor',
      ctor: `ts.binder[${leanStr(b.varName)}](ts.number${bounds.map((x) => `, ${x}`).join('')})`,
    };
  }
  if (b.domain !== 'int' && b.domain !== 'nat') return { kind: 'bare' };
  const named = (ty: string) =>
    ({
      kind: 'ctor',
      ctor: `ts.binder[${leanStr(b.varName)}](${ty})`,
    }) as const;
  const r = b.range;
  // No interval at all: the whole domain, which the generic proof stage
  // can attempt — nat keeps its nonnegativity in the binder.
  if (r === undefined) return named(b.domain === 'nat' ? 'ts.nat' : 'ts.int');
  // Lemma guarantees integer endpoint text for int/nat; a surprise still
  // cannot abort transcription — structuredProp's catch degrades it.
  const { lo, hi } = intInterval(b.domain, r);
  if (hi === undefined) {
    // Unbounded above: the DSL's only shapes are the whole int line and
    // the naturals. Any other floor would need a one-sided binder.
    if (lo === undefined) return named('ts.int');
    return lo === 0n ? named('ts.nat') : { kind: 'bare' };
  }
  // Unbounded below with a finite ceiling: substituting the safe-range
  // floor would prove a narrower statement than written.
  if (lo === undefined) return { kind: 'bare' };
  const clamped = clampedEndpoints(b);
  if (clamped.length > 0) return { kind: 'clamped', endpoints: clamped };
  return {
    kind: 'ctor',
    ctor: `ts.binder[${leanStr(b.varName)}](ts.int, ts.range(${lo}, ${hi + 1n}))`,
  };
}

/** Parse a formula atom's JS expression with tsc. The wrapping parentheses
 * keep statement-level ambiguities (object literals) out of play. */
function parseAtomExpr(
  js: string,
): { sf: ts.SourceFile; expr: ts.Expression } | undefined {
  const sf = ts.createSourceFile(
    'atom.ts',
    `(${js});`,
    ts.ScriptTarget.Latest,
    true,
  );
  // createSourceFile recovers from bad input; a lenient parse of a non-JS
  // atom would silently truncate it, so reject on any diagnostic.
  const diags = (sf as unknown as { parseDiagnostics: readonly unknown[] })
    .parseDiagnostics;
  if (diags.length > 0) return undefined;
  // A diagnostic-free parse of `(expr);` is exactly one expression statement.
  const stmt = sf.statements[0] as ts.ExpressionStatement;
  return { sf, expr: stmt.expression };
}

function unwrapParens(e: ts.Expression): ts.Expression {
  return ts.isParenthesizedExpression(e) ? unwrapParens(e.expression) : e;
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

/** Whether a guard atom is a desugared equation (`Object.is`, possibly
 * negated). The DSL's guard slot is a boolean expression with IEEE
 * semantics only — SameValue has no node there — and emitting the call
 * opaquely would misreport an in-spec formula as Inappropriate, so an
 * equation guard degrades the property to bare instead. */
function isEquationGuard(e: ts.Expression): boolean {
  const inner = unwrapParens(e);
  if (
    ts.isPrefixUnaryExpression(inner) &&
    inner.operator === ts.SyntaxKind.ExclamationToken
  ) {
    return equationSides(unwrapParens(inner.operand)) !== undefined;
  }
  return equationSides(inner) !== undefined;
}

type PropReading =
  | { kind: 'structured'; binders: string[]; body: string }
  | { kind: 'unsupported-range'; reason: string }
  | { kind: 'bare' };

/** The body shapes this slice can structure, as guard atoms around a
 * conclusion atom: a bare atom, or a top-level implication chain whose
 * antecedents and conclusion are all atoms — exactly the shape the refuter
 * lowers to fc.pre discards. Any other connective is undefined (bare). */
function chainReading(
  ast: Formula,
): { guards: string[]; conclusion: string } | undefined {
  if (ast.kind === 'atom') return { guards: [], conclusion: ast.js };
  if (ast.kind !== 'implication') return undefined;
  if (ast.consequent.kind !== 'atom') return undefined;
  const guards: string[] = [];
  for (const a of ast.antecedents) {
    if (a.kind !== 'atom') return undefined;
    guards.push(a.js);
  }
  return { guards, conclusion: ast.consequent.js };
}

/** The `ts_prop` reading of a Lemma formula: unbounded int/nat domains
 * structure like bounded ones; bare when this slice cannot express it
 * (non-integer domains, half-bounded ranges with no DSL binder shape,
 * connectives beyond a top-level implication chain of atoms, equation
 * guards, or a formula the Lemma parser rejects), unsupported-range
 * only when a safe-integer clamp is the SOLE blocker — an annotation this
 * slice could not have structured anyway degrades to bare, whatever its
 * ranges. The
 * exception is an interval the clamp emptied: with no domain left there
 * is nothing to attempt, so it is unsupported-range whatever the body. */
function structuredProp(formula: string): PropReading {
  try {
    const { binders, body } = parsePrefix(formula);
    const binderCtors: string[] = [];
    const clamped: string[] = [];
    for (const b of binders) {
      const lowered = binderConstructor(b);
      if (lowered.kind === 'bare') return { kind: 'bare' };
      if (lowered.kind === 'clamped') clamped.push(...lowered.endpoints);
      else binderCtors.push(lowered.ctor);
    }
    const chain = chainReading(parseBody(body));
    if (chain === undefined) return { kind: 'bare' };
    const parsed = parseAtomExpr(chain.conclusion);
    if (parsed === undefined) return { kind: 'bare' };
    const guardCtors: string[] = [];
    for (const g of chain.guards) {
      const gp = parseAtomExpr(g);
      if (gp === undefined) return { kind: 'bare' };
      if (isEquationGuard(gp.expr)) return { kind: 'bare' };
      guardCtors.push(transcribeExpr(unwrapParens(gp.expr), gp.sf));
    }
    if (clamped.length > 0) {
      return {
        kind: 'unsupported-range',
        reason: unsupportedRangeReason(clamped),
      };
    }
    const expr = unwrapParens(parsed.expr);
    const sides = equationSides(expr);
    const conclusionCtor =
      sides === undefined
        ? `ts.istrue(${transcribeExpr(expr, parsed.sf)})`
        : `ts.eq(${transcribeExpr(sides[0], parsed.sf)}, ${transcribeExpr(sides[1], parsed.sf)})`;
    const bodyCtor = guardCtors.reduceRight(
      (acc, g) => `ts.imp(${g}) { ${acc} }`,
      conclusionCtor,
    );
    return { kind: 'structured', binders: binderCtors, body: bodyCtor };
  } catch (e) {
    // A clamp-emptied interval leaves no domain to prove over, whatever
    // the body: unsupported-range, like its merely-clamped kin.
    if (e instanceof EmptyAfterClampError) {
      return {
        kind: 'unsupported-range',
        reason: unsupportedRangeReason(e.endpoints),
      };
    }
    // Transcription never aborts on a formula: anything else the Lemma
    // parsers reject degrades to the bare (NotTried) form.
    return { kind: 'bare' };
  }
}

/** An annotation the transcriber deliberately emitted no prove command
 * for; the CLI reports it NotTried with this kind and reason. */
export interface UntriedAnnotation {
  annotation: RawAnnotation;
  kind: 'unsupported-range';
  reason: string;
}

/** One annotation's `#thales_prove` block: the formula as a comment, then
 * the command — bare (`NotTried`) when the property has no structured
 * reading, and no command at all (an `untried` record instead) when the
 * range is unsupported. The identity triple matches pabst's: file,
 * qualified function name, property name. */
function proveBlock(
  a: RawAnnotation,
  file: string,
): { lines: string[]; untried?: UntriedAnnotation } {
  const fnName = qualifiedName(a.functionName, a.className, a.isStatic);
  const head =
    `#thales_prove ${leanStr(file)} ${leanStr(fnName)} ` +
    leanStr(a.propertyName);
  const comment =
    `-- @ensures{${a.propertyName}} ` + a.formula.replace(/\s+/g, ' ').trim();
  const reading = structuredProp(a.formula);
  if (reading.kind === 'unsupported-range') {
    return {
      lines: [
        comment,
        `-- not tried @ensures{${a.propertyName}} on ${fnName}: ${reading.reason}`,
      ],
      untried: { annotation: a, ...reading },
    };
  }
  if (reading.kind === 'bare') return { lines: [comment, head] };
  return {
    lines: [
      comment,
      `${head} :=`,
      `  ts.forall(${reading.binders.join(', ')}) {`,
      `    ${reading.body}`,
      '  }',
    ],
  };
}

/** One comment line per annotation extraction rejected: the artifact is the
 * ground truth, so what was NOT transcribed must be visible in it. */
function skippedComment(i: InvalidAnnotation, file: string): string {
  const fn = qualifiedName(i.functionName, i.className, i.isStatic);
  return `-- skipped @ensures{${i.propertyName}} on ${fn}: ${file}:${i.line}: ${i.message}`;
}

/** Comment out a statement's original source, line by line. */
function sourceComments(stmt: ts.Statement, sf: ts.SourceFile): string[] {
  return stmt
    .getText(sf)
    .split('\n')
    .map((line) => (line === '' ? '--' : `-- ${line}`));
}

/** A transcribed program plus what extraction found (and rejected) in it.
 * `untried` annotations appear in `annotations` too but got no prove
 * command, so no verdict will come back for them. */
export interface Transcription {
  lean: string;
  annotations: RawAnnotation[];
  invalid: InvalidAnnotation[];
  untried: UntriedAnnotation[];
}

/**
 * Pretty-print a TypeScript program into a `.lean` file of core DSL
 * constructors. `file` is a label only; parsing is syntax-only.
 */
export function transcribe(text: string, file: string): Transcription {
  const sf = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true);
  const blocks: string[][] = [['import ThalesDsl']];
  for (const stmt of sf.statements) {
    const defs = ts.isFunctionDeclaration(stmt)
      ? transcribeFunction(stmt, sf)
      : transcribeOtherDecl(stmt, sf);
    blocks.push([...sourceComments(stmt, sf), ...defs]);
  }
  const { annotations, invalid } = extractFromSource(text, file);
  const untried: UntriedAnnotation[] = [];
  for (const a of annotations) {
    const block = proveBlock(a, file);
    blocks.push(block.lines);
    if (block.untried !== undefined) untried.push(block.untried);
  }
  if (invalid.length > 0)
    blocks.push(invalid.map((i) => skippedComment(i, file)));
  return {
    lean: blocks.map((b) => b.join('\n')).join('\n\n') + '\n',
    annotations,
    invalid,
    untried,
  };
}

/** The `.lean` text alone; see `transcribe` for the full result. */
export function transcribeSource(text: string, file: string): string {
  return transcribe(text, file).lean;
}

/** Read a `.ts` file from disk and transcribe it; the path (as given) is
 * the annotations' identity `file`. */
export function transcribeFile(file: string): string {
  return transcribeSource(fs.readFileSync(file, 'utf8'), file);
}
