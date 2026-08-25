import * as fs from 'node:fs';
import * as path from 'node:path';
import ts from 'typescript';
import {
  type Binder,
  clampedEndpoints,
  EmptyAfterClampError,
  extractFromSource,
  intInterval,
  isClassDomain,
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

/** The Lean literal token for a numeric literal. tsc normalizes the
 * literal text (separators stripped, radix prefixes decimalized), and
 * toString prints the shortest round-tripping decimal, which Lean's
 * OfScientific reconstructs as the identical double. */
function numberToken(lit: ts.NumericLiteral): string {
  const n = Number(lit.text);
  if (!Number.isFinite(n)) return 'Infinity';
  return n.toString().replace('e+', 'e');
}

/** How a module's names reach the artifact: a name as written, mapped to
 * the name the `ts_def` defining it carries. A name the map does not
 * mention emits as written — every local, and the entry module's own
 * declarations. */
type NameMap = ReadonlyMap<string, string>;

/** The artifact name an identifier reference resolves to. */
function ref(name: string, names: NameMap): string {
  return names.get(name) ?? name;
}

/** `names` with locally bound spellings removed: a parameter, a const
 * binding, or a ∀-binder shadows the module-level name it repeats. */
function shadow(names: NameMap, locals: ReadonlySet<string>): NameMap {
  if (names.size === 0 || locals.size === 0) return names;
  const scoped = new Map(names);
  for (const l of locals) scoped.delete(l);
  return scoped;
}

function transcribeExpr(
  e: ts.Expression,
  sf: ts.SourceFile,
  names: NameMap,
): string {
  if (ts.isIdentifier(e)) return `ts.id[${leanStr(ref(e.text, names))}]`;
  if (ts.isNumericLiteral(e)) return `ts.num[${numberToken(e)}]`;
  if (
    ts.isPrefixUnaryExpression(e) &&
    e.operator === ts.SyntaxKind.MinusToken &&
    ts.isNumericLiteral(e.operand)
  ) {
    return `ts.num[-${numberToken(e.operand)}]`;
  }
  if (
    ts.isPrefixUnaryExpression(e) &&
    (e.operator === ts.SyntaxKind.MinusToken ||
      e.operator === ts.SyntaxKind.PlusToken)
  ) {
    const op = ts.tokenToString(e.operator)!;
    return `ts.unop[${leanStr(op)}](${transcribeExpr(e.operand, sf, names)})`;
  }
  if (ts.isParenthesizedExpression(e))
    return transcribeExpr(e.expression, sf, names);
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.getText(sf);
    const l = transcribeExpr(e.left, sf, names);
    const r = transcribeExpr(e.right, sf, names);
    return `ts.binop[${leanStr(op)}](${l}, ${r})`;
  }
  if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
    const args = e.arguments.map((a) => transcribeExpr(a, sf, names));
    const callee = leanStr(ref(e.expression.text, names));
    return `ts.call[${callee}](${args.join(', ')})`;
  }
  return opaque(e, sf);
}

/** Names a body binds itself, and whether each may be assigned. A branch's
 * arm gets its own copy: a binding made inside an arm dies with it, and a
 * redeclaration of a name from outside is refused rather than shadowed.
 * Separate from the module's `NameMap`, which says how a name reaches the
 * artifact rather than whether it can be written to. */
type Locals = Map<string, 'const' | 'mutable'>;

/** `ts.const`/`ts.let` lines for a declaration's declarators, or undefined
 * when any declarator falls outside the slice. `await using` shares the
 * Const flag, so the Using bit is excluded explicitly; `var` is
 * function-scoped and hoisted, which the lowering does not model. An
 * uninitialized `let` is left out too: reading one is only safe behind a
 * definite-assignment analysis this slice does not perform. */
function declarationLines(
  s: ts.VariableStatement,
  sf: ts.SourceFile,
  names: NameMap,
  locals: Locals,
): string[] | undefined {
  const flags = s.declarationList.flags;
  const isConst = (flags & ts.NodeFlags.Const) !== 0;
  const isLet = (flags & ts.NodeFlags.Let) !== 0;
  if (!isConst && !isLet) return undefined;
  if ((flags & ts.NodeFlags.Using) !== 0) return undefined;
  // Parser recovery can yield a declarator list with no declarators.
  if (s.declarationList.declarations.length === 0) return undefined;
  const lines: string[] = [];
  for (const d of s.declarationList.declarations) {
    if (!ts.isIdentifier(d.name)) return undefined;
    if (d.initializer === undefined) return undefined;
    if (d.type !== undefined && d.type.kind !== ts.SyntaxKind.NumberKeyword)
      return undefined;
    // Shadowing a name already bound here would make a join ambiguous: an
    // arm's own binding is what the tail would read back.
    if (locals.has(d.name.text)) return undefined;
    const ctor = isConst ? 'ts.const' : 'ts.let';
    const init = transcribeExpr(d.initializer, sf, names);
    lines.push(`${ctor}[${leanStr(d.name.text)}](${init})`);
    locals.set(d.name.text, isConst ? 'const' : 'mutable');
  }
  return lines;
}

/** The `ts.assign` line for a reassignment of a mutable local, or
 * undefined for anything else an expression statement can be — a call for
 * its effects, a compound assignment, a write to a const or to a name the
 * body did not bind. */
function assignmentLine(
  e: ts.Expression,
  sf: ts.SourceFile,
  names: NameMap,
  locals: Locals,
): string | undefined {
  if (!ts.isBinaryExpression(e)) return undefined;
  if (e.operatorToken.kind !== ts.SyntaxKind.EqualsToken) return undefined;
  const target = unwrapParens(e.left);
  if (!ts.isIdentifier(target)) return undefined;
  if (locals.get(target.text) !== 'mutable') return undefined;
  const value = transcribeExpr(e.right, sf, names);
  return `ts.assign[${leanStr(target.text)}](${value})`;
}

/** The error kind a `throw` carries. Only the constructor's name is
 * modeled: the message is a string the value model has nothing to say
 * about, and approximating it would put a fiction in the verdict. */
function errorKind(e: ts.Expression): string | undefined {
  const inner = unwrapParens(e);
  if (!ts.isNewExpression(inner)) return undefined;
  if (!ts.isIdentifier(inner.expression)) return undefined;
  return inner.expression.text;
}

/** The operators whose result the boolean channel accepts. Truthiness
 * coercion and the logical operators have no model, so a condition spelled
 * either way degrades its declaration instead of elaborating as a number. */
const COMPARISON_OPERATORS = new Set(['<', '<=', '>', '>=', '===', '!==']);

function conditionExpr(
  e: ts.Expression,
  sf: ts.SourceFile,
  names: NameMap,
): string {
  const inner = unwrapParens(e);
  if (
    ts.isBinaryExpression(inner) &&
    COMPARISON_OPERATORS.has(inner.operatorToken.getText(sf))
  ) {
    return transcribeExpr(inner, sf, names);
  }
  return opaque(inner, sf);
}

/** An `if` arm's statements, indented. A non-block arm is the one statement
 * it is, which is how an `else if` arrives: a nested `ts.if` alone in the
 * else arm. The arm's locals are a copy, so its bindings do not escape it. */
function armLines(
  stmt: ts.Statement,
  sf: ts.SourceFile,
  names: NameMap,
  locals: Locals,
): string[] {
  const body = ts.isBlock(stmt) ? stmt.statements : [stmt];
  return transcribeStmts(body, sf, names, new Map(locals)).map(
    (line) => `  ${line}`,
  );
}

function ifLines(
  s: ts.IfStatement,
  sf: ts.SourceFile,
  names: NameMap,
  locals: Locals,
): string[] {
  const lines = [
    `ts.if(${conditionExpr(s.expression, sf, names)}) {`,
    ...armLines(s.thenStatement, sf, names, locals),
  ];
  if (s.elseStatement === undefined) return [...lines, '}'];
  return [
    ...lines,
    '} else {',
    ...armLines(s.elseStatement, sf, names, locals),
    '}',
  ];
}

/** One statement's lines. `locals` is this list's own scope, which a
 * declaration extends in place for the statements after it. */
function transcribeStmt(
  s: ts.Statement,
  sf: ts.SourceFile,
  names: NameMap,
  locals: Locals,
): string[] {
  if (ts.isReturnStatement(s)) {
    // `return;` yields undefined, which a `number` function has no value
    // for and this slice does not model.
    if (s.expression === undefined) return [opaque(s, sf)];
    return [`ts.return(${transcribeExpr(s.expression, sf, names)})`];
  }
  if (ts.isThrowStatement(s)) {
    const kind = errorKind(s.expression);
    if (kind !== undefined) return [`ts.throw[${leanStr(kind)}]`];
  }
  if (ts.isVariableStatement(s)) {
    const lines = declarationLines(s, sf, names, locals);
    if (lines !== undefined) return lines;
  }
  if (ts.isExpressionStatement(s)) {
    const line = assignmentLine(s.expression, sf, names, locals);
    if (line !== undefined) return [line];
  }
  if (ts.isIfStatement(s)) return ifLines(s, sf, names, locals);
  return [opaque(s, sf)];
}

function transcribeStmts(
  statements: readonly ts.Statement[],
  sf: ts.SourceFile,
  names: NameMap,
  locals: Locals,
): string[] {
  return statements.flatMap((s) => transcribeStmt(s, sf, names, locals));
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

/** The names a function body binds itself, which shadow the module's. The
 * walk goes into branches: a binding made inside an arm shadows just as
 * one at the top of the body does. */
function functionLocals(
  fn: ts.FunctionDeclaration,
  body: readonly ts.Statement[],
): Set<string> {
  const locals = new Set<string>();
  for (const p of fn.parameters) locals.add((p.name as ts.Identifier).text);
  const walk = (stmts: readonly ts.Statement[]): void => {
    for (const s of stmts) {
      if (ts.isVariableStatement(s)) {
        for (const d of s.declarationList.declarations)
          for (const id of bindingIdentifiers(d.name)) locals.add(id.text);
      } else if (ts.isBlock(s)) {
        walk(s.statements);
      } else if (ts.isIfStatement(s)) {
        walk([s.thenStatement]);
        if (s.elseStatement !== undefined) walk([s.elseStatement]);
      }
    }
  };
  walk(body);
  return locals;
}

function transcribeFunction(
  fn: ts.FunctionDeclaration,
  sf: ts.SourceFile,
  scope: ModuleScope,
): string[] {
  if (fn.name === undefined) return [];
  const name = scope.defName(fn.name.text);
  const blocker = signatureBlocker(fn);
  if (blocker !== undefined) {
    return [opaqueDef(name, blocker.kind, blocker, sf)];
  }
  const params = fn.parameters.map(
    (p) => `ts.param[${leanStr((p.name as ts.Identifier).text)}](ts.number)`,
  );
  const stmts = fn.body?.statements ?? [];
  const names = shadow(scope.names, functionLocals(fn, stmts));
  // Parameters are assignable, the way JavaScript has them.
  const locals: Locals = new Map(
    fn.parameters.map((p) => [
      (p.name as ts.Identifier).text,
      'mutable' as const,
    ]),
  );
  const body = transcribeStmts(stmts, sf, names, locals).map(
    (line) => `  ${line}`,
  );
  return [
    `ts_def ${leanStr(name)} := ts.fn(${params.join(', ')}) : ts.number {`,
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

/** Opaque ts_defs for every name a non-function declaration binds. An
 * import name whose module was inlined binds no def of its own: the
 * exporting module already carries the definition. */
function transcribeOtherDecl(
  stmt: ts.Statement,
  sf: ts.SourceFile,
  scope: ModuleScope,
): string[] {
  const def = (name: string, at: ts.Node) =>
    opaqueDef(scope.defName(name), stmt.kind, at, sf);
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
        for (const el of bindings.elements) {
          if (scope.inlined.has(el.name.text)) continue;
          defs.push(def(el.name.text, el.name));
        }
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

/** The top-level names a non-import declaration binds — what a reference
 * elsewhere in the module can name. Class members are not among them: a
 * member's ts_def name is synthesized, never written as an identifier. */
function declaredNames(stmt: ts.Statement): string[] {
  if (ts.isVariableStatement(stmt)) {
    return stmt.declarationList.declarations.flatMap((d) =>
      bindingIdentifiers(d.name).map((id) => id.text),
    );
  }
  const name = (stmt as { name?: ts.Node }).name;
  return name !== undefined && ts.isIdentifier(name) ? [name.text] : [];
}

/** How one module's top-level names reach the artifact. */
interface ModuleScope {
  /** Every top-level name the module binds. */
  names: NameMap;
  /** Import-bound names whose module was inlined: the definition travels
   * with the exporting module, so this one emits none. */
  inlined: ReadonlySet<string>;
  /** The ts_def name a declaration in this module carries. */
  defName: (name: string) => string;
}

/** Reads a module's text by absolute path, or undefined when there is no
 * such file. Injectable, so a closure can be transcribed without a disk. */
export type ModuleReader = (file: string) => string | undefined;

const diskReader: ModuleReader = (file) => {
  try {
    return fs.readFileSync(file, 'utf8');
  } catch {
    return undefined;
  }
};

/** A specifier names the file nodeNext will emit; the TypeScript source it
 * was written as is what resolution wants, and it wins over a sibling
 * spelled the way the specifier is. */
const SOURCE_EXTENSIONS: Record<string, string[]> = {
  '.mjs': ['.mts'],
  '.cjs': ['.cts'],
  '.js': ['.ts', '.tsx'],
};

/** The file a relative specifier names, or undefined for a bare specifier
 * (a package or a builtin) and for one that reaches no file. */
function resolveImport(
  specifier: string,
  from: string,
  reader: ModuleReader,
): { file: string; text: string } | undefined {
  if (!/^\.\.?\//.test(specifier)) return undefined;
  const ext = path.extname(specifier);
  const stem = specifier.slice(0, specifier.length - ext.length);
  const spellings = [
    ...(SOURCE_EXTENSIONS[ext] ?? []).map((e) => stem + e),
    specifier,
  ];
  for (const spelling of spellings) {
    const file = path.resolve(path.dirname(from), spelling);
    const text = reader(file);
    if (text !== undefined) return { file, text };
  }
  return undefined;
}

/** The prefix a dependency's ts_def names carry: its path relative to the
 * entry file, which is unique to it within the entry's artifact. */
function moduleQualifier(entryDir: string, file: string): string {
  return path.relative(entryDir, file).split(path.sep).join('/');
}

/** One entry file's dependency-closure walk. Artifacts are self-contained,
 * so the closure is inlined into the entry's own artifact rather than
 * imported: every module it reaches contributes its declarations under
 * module-qualified names. */
interface Closure {
  reader: ModuleReader;
  /** What module qualifiers are relative to: the entry file's directory. */
  entryDir: string;
  /** Modules already inlined, by absolute path, with their name maps. */
  done: Map<string, NameMap>;
  /** Modules whose walk has not finished: an import reaching back into one
   * closes a cycle. */
  active: Set<string>;
  /** Blocks emitted so far, each dependency before the module using it. */
  blocks: string[][];
}

/** Inline `target` if it is not already in, and answer its name map. */
function inlineModule(
  target: { file: string; text: string },
  c: Closure,
): NameMap {
  const done = c.done.get(target.file);
  if (done !== undefined) return done;
  c.active.add(target.file);
  const names = walkModule(
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
 * module's definitions when the specifier resolves, opaquely otherwise —
 * a bare specifier, a relative one that reaches no file, a name that
 * module does not declare, or a specifier reaching a module still being
 * walked, which is an import cycle degrading at the edge that closes it.
 * Default and namespace imports name a module object, which the model has
 * no shape for, so they stay opaque however their specifier resolves. */
function bindImport(
  stmt: ts.ImportDeclaration,
  from: string,
  names: Map<string, string>,
  inlined: Set<string>,
  defName: (name: string) => string,
  c: Closure,
): void {
  const clause = stmt.importClause;
  if (clause === undefined) return;
  if (clause.name !== undefined)
    names.set(clause.name.text, defName(clause.name.text));
  const bindings = clause.namedBindings;
  if (bindings === undefined) return;
  if (ts.isNamespaceImport(bindings)) {
    names.set(bindings.name.text, defName(bindings.name.text));
    return;
  }
  const specifier = stmt.moduleSpecifier;
  const target = ts.isStringLiteral(specifier)
    ? resolveImport(specifier.text, from, c.reader)
    : undefined;
  const exported =
    target === undefined || c.active.has(target.file)
      ? undefined
      : inlineModule(target, c);
  for (const el of bindings.elements) {
    const local = el.name.text;
    const to = exported?.get((el.propertyName ?? el.name).text);
    if (to === undefined) {
      names.set(local, defName(local));
    } else {
      names.set(local, to);
      inlined.add(local);
    }
  }
}

/** Transcribe one module and, ahead of it, everything it imports. `label`
 * is what positions are reported against; `qualifier` is empty for the
 * entry file, whose names are the ones annotations are written about and
 * so keep their source spelling. */
function walkModule(
  file: string,
  label: string,
  text: string,
  qualifier: string,
  c: Closure,
): NameMap {
  const sf = ts.createSourceFile(label, text, ts.ScriptTarget.Latest, true);
  const defName = (name: string) =>
    qualifier === '' ? name : `${qualifier}::${name}`;
  const names = new Map<string, string>();
  const inlined = new Set<string>();
  // Bindings first, and dependencies with them: a call may precede the
  // declaration it names, and every dependency's blocks must precede this
  // module's, since the elaborator resolves a call where it stands.
  for (const stmt of sf.statements) {
    if (ts.isImportDeclaration(stmt)) {
      bindImport(stmt, file, names, inlined, defName, c);
    } else {
      for (const name of declaredNames(stmt)) names.set(name, defName(name));
    }
  }
  const scope: ModuleScope = { names, inlined, defName };
  if (qualifier !== '') c.blocks.push([`-- module ${qualifier}`]);
  for (const stmt of sf.statements) {
    const defs = ts.isFunctionDeclaration(stmt)
      ? transcribeFunction(stmt, sf, scope)
      : transcribeOtherDecl(stmt, sf, scope);
    c.blocks.push([...sourceComments(stmt, sf), ...defs]);
  }
  return names;
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
  | { kind: 'class-binder'; reason: string }
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
function structuredProp(formula: string, moduleNames: NameMap): PropReading {
  try {
    const { binders, body } = parsePrefix(formula);
    // Outside the model, not a missing shape: the property is refused with
    // the construct named, whatever else the formula contains.
    const classBinder = binders.find((b) => isClassDomain(b.domain));
    if (classBinder !== undefined && isClassDomain(classBinder.domain)) {
      return {
        kind: 'class-binder',
        reason: `class-valued binder '${classBinder.domain.className}' is not yet modeled`,
      };
    }
    const names = shadow(moduleNames, new Set(binders.map((b) => b.varName)));
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
      guardCtors.push(transcribeExpr(unwrapParens(gp.expr), gp.sf, names));
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
        ? `ts.istrue(${transcribeExpr(expr, parsed.sf, names)})`
        : `ts.eq(${transcribeExpr(sides[0], parsed.sf, names)}, ` +
          `${transcribeExpr(sides[1], parsed.sf, names)})`;
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
 * for; the CLI reports it from the kind — NotTried for unsupported-range,
 * Inappropriate for class-binder — with this reason. */
export interface UntriedAnnotation {
  annotation: RawAnnotation;
  kind: 'unsupported-range' | 'class-binder';
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
  names: NameMap,
): { lines: string[]; untried?: UntriedAnnotation } {
  const fnName = qualifiedName(a.functionName, a.className, a.isStatic);
  const head =
    `#thales_prove ${leanStr(file)} ${leanStr(fnName)} ` +
    leanStr(a.propertyName);
  const comment =
    `-- @ensures{${a.propertyName}} ` + a.formula.replace(/\s+/g, ' ').trim();
  const reading = structuredProp(a.formula, names);
  if (reading.kind === 'unsupported-range') {
    return {
      lines: [
        comment,
        `-- not tried @ensures{${a.propertyName}} on ${fnName}: ${reading.reason}`,
      ],
      untried: { annotation: a, ...reading },
    };
  }
  if (reading.kind === 'class-binder') {
    return {
      lines: [
        comment,
        `-- inappropriate @ensures{${a.propertyName}} on ${fnName}: ${reading.reason}`,
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
 * constructors, with the closure of its relative imports inlined ahead of
 * it. `file` locates the entry against the module tree `reader` reads, and
 * labels the annotations; parsing is syntax-only. Only the entry's own
 * annotations are proved — a dependency's belong to its own artifact.
 */
export function transcribe(
  text: string,
  file: string,
  reader: ModuleReader = diskReader,
): Transcription {
  const entry = path.resolve(file);
  const closure: Closure = {
    reader,
    entryDir: path.dirname(entry),
    done: new Map(),
    active: new Set([entry]),
    blocks: [['import ThalesDsl']],
  };
  const names = walkModule(entry, file, text, '', closure);
  const { annotations, invalid } = extractFromSource(text, file);
  const untried: UntriedAnnotation[] = [];
  for (const a of annotations) {
    const block = proveBlock(a, file, names);
    closure.blocks.push(block.lines);
    if (block.untried !== undefined) untried.push(block.untried);
  }
  if (invalid.length > 0)
    closure.blocks.push(invalid.map((i) => skippedComment(i, file)));
  return {
    lean: closure.blocks.map((b) => b.join('\n')).join('\n\n') + '\n',
    annotations,
    invalid,
    untried,
  };
}

/** The `.lean` text alone; see `transcribe` for the full result. */
export function transcribeSource(
  text: string,
  file: string,
  reader?: ModuleReader,
): string {
  return transcribe(text, file, reader).lean;
}

/** Read a `.ts` file from disk and transcribe it; the path (as given) is
 * the annotations' identity `file`. */
export function transcribeFile(file: string): string {
  return transcribeSource(fs.readFileSync(file, 'utf8'), file);
}
