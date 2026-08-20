import * as fs from 'node:fs';
import ts from 'typescript';
import type { Binder } from '../../../../lemma/src/binder.js';
import {
  intBounds,
  SAFE_INTEGER_RANGE,
} from '../../../../lemma/src/domains.js';
import {
  extractFromSource,
  type InvalidAnnotation,
  type RawAnnotation,
} from '../../../../lemma/src/extract.js';
import { parseBody } from '../../../../lemma/src/formula-parser.js';
import { parsePrefix } from '../../../../lemma/src/prefix-parser.js';
import { qualifiedName } from '../../../../lemma/src/qualified-name.js';

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

function transcribeStmt(s: ts.Statement, sf: ts.SourceFile): string {
  if (ts.isReturnStatement(s) && s.expression !== undefined) {
    return `ts.return(${transcribeExpr(s.expression, sf)})`;
  }
  return opaque(s, sf);
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
  const body = (fn.body?.statements ?? []).map(
    (s) => `  ${transcribeStmt(s, sf)}`,
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

function unsupportedRangeReason(endpoints: string[]): string {
  const one = endpoints.length === 1;
  return (
    `endpoint${one ? '' : 's'} ${endpoints.join(' and ')} ` +
    `exceed${one ? 's' : ''} ${SAFE_INTEGER_RANGE}`
  );
}

/** The `ballIco`-style lowering of a binder: inclusive lo, exclusive hi. */
function binderConstructor(b: Binder): BinderLowering {
  if (b.domain !== 'int' && b.domain !== 'nat') return { kind: 'bare' };
  const r = b.range;
  if (r === undefined || r.min === undefined || r.max === undefined) {
    return { kind: 'bare' };
  }
  // Lemma guarantees integer endpoint text for int/nat; a surprise still
  // cannot abort transcription — structuredProp's catch degrades it.
  const { lo, hi, clampedLo, clampedHi } = intBounds(b.domain, r);
  if (clampedLo || clampedHi) {
    return {
      kind: 'clamped',
      endpoints: [...(clampedLo ? [r.min] : []), ...(clampedHi ? [r.max] : [])],
    };
  }
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

type PropReading =
  | { kind: 'structured'; binders: string[]; body: string }
  | { kind: 'unsupported-range'; reason: string }
  | { kind: 'bare' };

/** The `ts_prop` reading of a Lemma formula: bare when this slice cannot
 * express it (non-integer domains, unbounded ranges, connectives, or a
 * formula the Lemma parser rejects), unsupported-range only when a
 * safe-integer clamp is the SOLE blocker — an annotation this slice could
 * not have structured anyway degrades to bare, whatever its ranges. */
function structuredProp(formula: string): PropReading {
  try {
    const { binders, body } = parsePrefix(formula);
    const binderCtors: string[] = [];
    const clampedEndpoints: string[] = [];
    for (const b of binders) {
      const lowered = binderConstructor(b);
      if (lowered.kind === 'bare') return { kind: 'bare' };
      if (lowered.kind === 'clamped')
        clampedEndpoints.push(...lowered.endpoints);
      else binderCtors.push(lowered.ctor);
    }
    const ast = parseBody(body);
    if (ast.kind !== 'atom') return { kind: 'bare' };
    const parsed = parseAtomExpr(ast.js);
    if (parsed === undefined) return { kind: 'bare' };
    if (clampedEndpoints.length > 0) {
      return {
        kind: 'unsupported-range',
        reason: unsupportedRangeReason(clampedEndpoints),
      };
    }
    const expr = unwrapParens(parsed.expr);
    const sides = equationSides(expr);
    const bodyCtor =
      sides === undefined
        ? `ts.istrue(${transcribeExpr(expr, parsed.sf)})`
        : `ts.eq(${transcribeExpr(sides[0], parsed.sf)}, ${transcribeExpr(sides[1], parsed.sf)})`;
    return { kind: 'structured', binders: binderCtors, body: bodyCtor };
  } catch {
    // Transcription never aborts on a formula: anything the Lemma parsers
    // reject degrades to the bare (NotTried) form.
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
