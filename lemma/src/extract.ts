import ts from "typescript";
import * as fs from "node:fs";
import { qualifiedName } from "./qualified-name.js";
import type { ClassInfo, ClassTable } from "./class-domain.js";
import type { CtorParam, GenerablePrimitive } from "./binder.js";

export interface RawAnnotation {
  propertyName: string;
  functionName: string;
  className?: string;
  isStatic?: boolean;
  formula: string;
  line: number;
}

/**
 * An annotation whose input is malformed — the SZS `InputError` cases.
 * Extraction collects these instead of throwing, so a run can report the
 * offender per annotation while sound annotations still get verdicts.
 * Identity is best-effort: subjects and properties without a proper name are
 * labeled with placeholders (`<anonymous>`, `<computed>`, `<unnamed>`) and
 * the message states what is unsupported.
 */
export interface InvalidAnnotation {
  propertyName: string;
  functionName: string;
  className?: string;
  isStatic?: boolean;
  line: number;
  message: string;
}

export interface ExtractResult {
  file: string;
  exports: Set<string>;
  /** Named class declarations, as class-domain resolution sees them. */
  classes: ClassTable;
  annotations: RawAnnotation[];
  invalid: InvalidAnnotation[];
}

// The `@ensures` tag name is matched via the JSDoc AST; this only peels the
// `{name}` prefix off the tag's comment text, leaving the formula as the rest.
const ENSURES_NAME = /^\{\s*([A-Za-z_][A-Za-z0-9_]*)\s*\}([\s\S]*)$/;

interface EnsuresMatch {
  propertyName: string;
  formula: string;
  line: number;
}

interface EnsuresScan {
  matches: EnsuresMatch[];
  /** Lines of `@ensures` tags whose `{name}` prefix is missing or malformed. */
  unnamed: number[];
}

/** Read a source file from disk and extract its annotations. */
export function extract(file: string): ExtractResult {
  return extractFromSource(fs.readFileSync(file, "utf8"), file);
}

/**
 * Extract `@ensures` annotations and exported names from already-loaded source
 * text. `file` is only a label — for diagnostics and the returned `file` field —
 * so this is pure and testable without touching disk.
 */
export function extractFromSource(text: string, file: string): ExtractResult {
  const sf = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true);
  const exportsSet = collectExports(sf);
  const annotations: RawAnnotation[] = [];
  const invalid: InvalidAnnotation[] = [];

  for (const stmt of sf.statements) {
    if (ts.isClassDeclaration(stmt)) {
      collectClassAnnotations(stmt, sf, exportsSet, file, annotations, invalid);
      continue;
    }
    const fnName = functionNameOf(stmt);
    if (!fnName) continue;
    const { matches, unnamed } = ensuresComments(stmt, sf);
    for (const line of unnamed) {
      invalid.push({
        propertyName: "<unnamed>",
        functionName: fnName,
        line,
        message: unnamedMessage(`function '${fnName}'`, file),
      });
    }
    for (const m of matches) {
      annotations.push({
        propertyName: m.propertyName,
        functionName: fnName,
        formula: m.formula,
        line: m.line,
      });
    }
  }
  return {
    file,
    exports: exportsSet,
    classes: collectClasses(sf, exportsSet),
    ...resolveDuplicates(annotations, invalid, file),
  };
}

function collectClasses(
  sf: ts.SourceFile,
  exportsSet: Set<string>,
): ClassTable {
  const classes: ClassTable = new Map();
  for (const stmt of sf.statements) {
    if (!ts.isClassDeclaration(stmt) || stmt.name === undefined) continue;
    const name = stmt.name.text;
    const info: ClassInfo = {
      exported:
        hasModifier(stmt, ts.SyntaxKind.ExportKeyword) || exportsSet.has(name),
      defaultExport: hasModifier(stmt, ts.SyntaxKind.DefaultKeyword),
      ...analyzeCtor(stmt, sf),
    };
    classes.set(name, info);
  }
  return classes;
}

const PARAM_TYPES: Partial<Record<ts.SyntaxKind, GenerablePrimitive>> = {
  [ts.SyntaxKind.NumberKeyword]: "number",
  [ts.SyntaxKind.BooleanKeyword]: "boolean",
  [ts.SyntaxKind.StringKeyword]: "string",
  [ts.SyntaxKind.BigIntKeyword]: "bigint",
};

/** A constructor's parameters as generation sees them, or why it refuses.
 * The refusal names the offending parameter: the diagnostic must let the
 * author fix the constructor without re-deriving the analysis. */
function analyzeCtor(
  cls: ts.ClassDeclaration,
  sf: ts.SourceFile,
): { ctorParams: CtorParam[] } | { ctorProblem: string } {
  const ctors = cls.members.filter(ts.isConstructorDeclaration);
  if (ctors.length > 1) {
    return {
      ctorProblem: "overloaded constructor (no single generable signature)",
    };
  }
  const ctor = ctors[0];
  if (ctor === undefined) return { ctorParams: [] };
  const params: CtorParam[] = [];
  for (const p of ctor.parameters) {
    if (!ts.isIdentifier(p.name)) {
      return { ctorProblem: "a constructor parameter is destructured" };
    }
    const name = p.name.text;
    if (p.dotDotDotToken !== undefined) {
      return {
        ctorProblem: `constructor parameter '${name}' is a rest parameter`,
      };
    }
    if (p.questionToken !== undefined) {
      return { ctorProblem: `constructor parameter '${name}' is optional` };
    }
    if (p.initializer !== undefined) {
      return {
        ctorProblem: `constructor parameter '${name}' has a default value`,
      };
    }
    if (p.type === undefined) {
      return {
        ctorProblem: `constructor parameter '${name}' has no type annotation`,
      };
    }
    const domain = PARAM_TYPES[p.type.kind];
    if (domain === undefined) {
      return {
        ctorProblem:
          `constructor parameter '${name}' has type '${p.type.getText(sf)}' — ` +
          `constructor parameters must be annotated number, boolean, string, or bigint`,
      };
    }
    params.push({ name, domain });
  }
  return { ctorParams: params };
}

/** The identity an annotation claims, as a collision key. */
function identityKey(a: {
  propertyName: string;
  functionName: string;
  className?: string;
  isStatic?: boolean;
}): string {
  return `${qualifiedName(a.functionName, a.className, a.isStatic)}\0${a.propertyName}`;
}

/**
 * A duplicated property name makes the identity ambiguous, so no claimant
 * can be attributed a verdict: the valid claimants collapse into a single
 * invalid entry for that identity. Invalid claimants count toward the
 * ambiguity and are deduplicated by identity for the same reason — unless
 * the identity contains a placeholder, which can cover distinct subjects.
 */
function resolveDuplicates(
  annotations: RawAnnotation[],
  invalid: InvalidAnnotation[],
  file: string,
): { annotations: RawAnnotation[]; invalid: InvalidAnnotation[] } {
  const counts = new Map<string, number>();
  for (const a of [...annotations, ...invalid]) {
    const key = identityKey(a);
    counts.set(key, (counts.get(key) ?? 0) + 1);
  }

  const kept: RawAnnotation[] = [];
  const out: InvalidAnnotation[] = [];
  const emitted = new Set<string>();
  for (const a of annotations) {
    const key = identityKey(a);
    const n = counts.get(key)!;
    if (n === 1) {
      kept.push(a);
      continue;
    }
    if (emitted.has(key)) continue;
    emitted.add(key);
    const subject =
      a.className === undefined
        ? `function '${a.functionName}'`
        : `member '${qualifiedName(a.functionName, a.className, a.isStatic)}'`;
    out.push({
      propertyName: a.propertyName,
      functionName: a.functionName,
      ...(a.className !== undefined
        ? { className: a.className, isStatic: a.isStatic }
        : {}),
      line: a.line,
      message: `duplicate property name '${a.propertyName}' on ${subject} in ${file} (declared ${n} times)`,
    });
  }
  for (const i of invalid) {
    // A placeholder label can cover several distinct subjects, so identity
    // dedup would swallow real entries — emit those verbatim.
    if (!hasPlaceholderIdentity(i)) {
      const key = identityKey(i);
      if (emitted.has(key)) continue;
      emitted.add(key);
    }
    out.push(i);
  }
  return { annotations: kept, invalid: out };
}

function hasPlaceholderIdentity(a: InvalidAnnotation): boolean {
  return (
    a.propertyName === "<unnamed>" ||
    a.functionName === "<computed>" ||
    a.className === "<anonymous>"
  );
}

function unnamedMessage(subject: string, file: string): string {
  return `@ensures on ${subject} in ${file} has a missing or malformed {name} prefix (expected '@ensures{name} <formula>')`;
}

function ensuresComments(node: ts.Node, sf: ts.SourceFile): EnsuresScan {
  const matches: EnsuresMatch[] = [];
  const unnamed: number[] = [];
  for (const tag of ts.getJSDocTags(node)) {
    if (tag.tagName.escapedText !== "ensures") continue;
    const comment = ts.getTextOfJSDocComment(tag.comment)?.trim() ?? "";
    const m = ENSURES_NAME.exec(comment);
    const line = sf.getLineAndCharacterOfPosition(tag.pos).line + 1;
    if (!m) {
      unnamed.push(line);
      continue;
    }
    matches.push({ propertyName: m[1]!, formula: m[2]!.trim(), line });
  }
  return { matches, unnamed };
}

function collectClassAnnotations(
  cls: ts.ClassDeclaration,
  sf: ts.SourceFile,
  exportsSet: Set<string>,
  file: string,
  annotations: RawAnnotation[],
  invalid: InvalidAnnotation[],
): void {
  const className = cls.name?.text;
  for (const member of cls.members) {
    const { matches, unnamed } = ensuresComments(member, sf);
    if (matches.length === 0 && unnamed.length === 0) continue;
    const label = memberLabel(member);
    const isStatic = hasModifier(member, ts.SyntaxKind.StaticKeyword);
    for (const line of unnamed) {
      const subject =
        className === undefined
          ? `member '${label}' of an anonymous class`
          : `member '${label}' of class '${className}'`;
      invalid.push({
        propertyName: "<unnamed>",
        functionName: label,
        className: className ?? "<anonymous>",
        isStatic,
        line,
        message: unnamedMessage(subject, file),
      });
    }
    if (matches.length === 0) continue;
    // Every detected annotation gets an entry, even when the subject has no
    // proper name: placeholder labels (`<anonymous>`, `<computed>`) keep the
    // identity best-effort and the message states what is unsupported.
    const problem =
      className === undefined
        ? `@ensures on member '${label}' of an anonymous class in ${file} (anonymous classes are not supported)`
        : !isEligibleMember(member)
          ? ineligibleMessage(member, label, className, file)
          : !exportsSet.has(className)
            ? `@ensures on member '${label}' of class '${className}', which is not exported from ${file}`
            : undefined;
    if (problem !== undefined) {
      for (const m of matches) {
        invalid.push({
          propertyName: m.propertyName,
          functionName: label,
          className: className ?? "<anonymous>",
          isStatic,
          line: m.line,
          message: problem,
        });
      }
      continue;
    }
    for (const m of matches) {
      annotations.push({
        propertyName: m.propertyName,
        functionName: label,
        className: className!,
        isStatic,
        formula: m.formula,
        line: m.line,
      });
    }
  }
}

/** The member kinds an @ensures may attach to: a method, a getter, or the
 * constructor. Setters are excluded — a property about a write has no value to
 * speak of. A constructor has no name to check; the other two must be named by
 * a plain identifier, so `#private` and computed names fall out here. */
type EligibleMember =
  ts.MethodDeclaration | ts.GetAccessorDeclaration | ts.ConstructorDeclaration;

function isEligibleMember(member: ts.ClassElement): member is EligibleMember {
  const named =
    ts.isMethodDeclaration(member) || ts.isGetAccessorDeclaration(member);
  if (!named && !ts.isConstructorDeclaration(member)) return false;
  if (named && !ts.isIdentifier(member.name)) return false;
  return (
    isPublic(member) && !hasModifier(member, ts.SyntaxKind.AbstractKeyword)
  );
}

function isPublic(member: ts.ClassElement): boolean {
  if (hasModifier(member, ts.SyntaxKind.PrivateKeyword)) return false;
  if (hasModifier(member, ts.SyntaxKind.ProtectedKeyword)) return false;
  return !(member.name !== undefined && ts.isPrivateIdentifier(member.name));
}

function ineligibleMessage(
  member: ts.ClassElement,
  label: string,
  className: string,
  file: string,
): string {
  const attachable =
    ts.isMethodDeclaration(member) ||
    ts.isGetAccessorDeclaration(member) ||
    ts.isConstructorDeclaration(member);
  if (attachable && !isPublic(member)) {
    return `@ensures on non-public member '${label}' of class '${className}' in ${file}`;
  }
  return (
    `@ensures on unsupported member '${label}' of class '${className}' in ${file} ` +
    `(setters, abstract, computed-name, and non-method members are not supported)`
  );
}

function memberLabel(member: ts.ClassElement): string {
  const name = member.name;
  if (
    name &&
    (ts.isIdentifier(name) ||
      ts.isPrivateIdentifier(name) ||
      ts.isStringLiteral(name))
  ) {
    return name.text;
  }
  if (ts.isConstructorDeclaration(member)) return "constructor";
  return "<computed>";
}

function hasModifier(node: ts.Node, kind: ts.SyntaxKind): boolean {
  const mods = ts.canHaveModifiers(node) ? ts.getModifiers(node) : undefined;
  return mods?.some((m) => m.kind === kind) ?? false;
}

function functionNameOf(stmt: ts.Statement): string | undefined {
  if (ts.isFunctionDeclaration(stmt) && stmt.name) return stmt.name.text;
  if (ts.isVariableStatement(stmt)) {
    const decl = stmt.declarationList.declarations[0];
    if (
      decl &&
      ts.isIdentifier(decl.name) &&
      decl.initializer &&
      (ts.isArrowFunction(decl.initializer) ||
        ts.isFunctionExpression(decl.initializer))
    ) {
      return decl.name.text;
    }
  }
  return undefined;
}

function collectExports(sf: ts.SourceFile): Set<string> {
  const out = new Set<string>();
  for (const stmt of sf.statements) {
    const mods = ts.canHaveModifiers(stmt) ? ts.getModifiers(stmt) : undefined;
    const isExported = mods?.some(
      (m) => m.kind === ts.SyntaxKind.ExportKeyword,
    );
    if (isExported) {
      if (ts.isFunctionDeclaration(stmt) && stmt.name) out.add(stmt.name.text);
      else if (ts.isClassDeclaration(stmt) && stmt.name)
        out.add(stmt.name.text);
      else if (ts.isVariableStatement(stmt)) {
        for (const d of stmt.declarationList.declarations) {
          if (ts.isIdentifier(d.name)) out.add(d.name.text);
        }
      }
    }
    if (
      ts.isExportDeclaration(stmt) &&
      stmt.exportClause &&
      ts.isNamedExports(stmt.exportClause)
    ) {
      for (const e of stmt.exportClause.elements) out.add(e.name.text);
    }
  }
  return out;
}
