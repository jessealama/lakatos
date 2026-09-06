import {
  annotationKey,
  type ClassCtorDomain,
  clampedEndpoints,
  type ClassTable,
  collectAtoms,
  EmptyAfterClampError,
  extract,
  freeIdentifiers,
  type InvalidAnnotation,
  isClassCtorDomain,
  isClassDomain,
  LemmaError,
  parseBody,
  parsePrefix,
  type RawAnnotation,
  resolveClassBinders,
  unsupportedRangeReason,
} from "../../../lemma/src/index.js";
import { enumerationCases } from "./enumerate.js";
import { lowerTop } from "./lower.js";
import type { PropertySpec } from "./ir.js";

/** An annotation the refuter will not test: a binder's domain is not
 * representable as written, so generating over the clamped one would
 * silently test a narrower statement. */
export interface UntriedProperty {
  functionName: string;
  className?: string;
  isStatic?: boolean;
  name: string;
  reason: string;
}

export interface BuildResult {
  specs: PropertySpec[];
  /** Extraction-level input errors, reported per annotation (InputError). */
  invalid: InvalidAnnotation[];
  /** Annotations refused before codegen, reported per annotation (NotTried). */
  untried: UntriedProperty[];
}

export function buildSpecs(
  file: string,
  refused: ReadonlySet<string> = new Set(),
): BuildResult {
  const { exports, classes, annotations: all, invalid } = extract(file);
  // A refused annotation is the CLI's InputError; nothing here mentions it.
  const annotations = all.filter((a) => !refused.has(annotationKey(file, a)));
  const specs: PropertySpec[] = [];
  const untried: UntriedProperty[] = [];
  const refuse = (a: RawAnnotation, endpoints: string[]) =>
    untried.push({
      functionName: a.functionName,
      className: a.className,
      isStatic: a.isStatic,
      name: a.propertyName,
      reason: unsupportedRangeReason(endpoints),
    });
  for (const a of annotations) {
    try {
      const spec = buildSpec(a, exports, classes, file);
      // Asked after the spec is built, so an annotation this engine could
      // not have tested anyway keeps its own diagnostic: the clamp is
      // reported only when it is the sole blocker.
      const clamped = spec.binders.flatMap(clampedEndpoints);
      if (clamped.length > 0) refuse(a, clamped);
      else specs.push(spec);
    } catch (e) {
      // Before the LemmaError arm: EmptyAfterClampError extends it.
      if (e instanceof EmptyAfterClampError) {
        refuse(a, e.endpoints);
        continue;
      }
      if (e instanceof LemmaError) {
        throw new LemmaError(
          `${file}:${a.line}: @ensures{${a.propertyName}}: ${e.message}`,
          { cause: e },
        );
      }
      throw e;
    }
  }
  return { specs, invalid, untried };
}

function buildSpec(
  a: RawAnnotation,
  exports: Set<string>,
  classes: ClassTable,
  file: string,
): PropertySpec {
  const { binders, body } = parsePrefix(a.formula);
  resolveClassBinders(binders, classes, file);
  const ast = parseBody(body);
  const { preconditions, body: loweredBody } = lowerTop(ast);
  const boundVars = new Set(binders.map((b) => b.varName));
  const idents = new Set<string>();
  for (const atom of collectAtoms(ast)) {
    for (const id of freeIdentifiers(atom)) idents.add(id);
  }
  // The generated spec imports what the atoms name from the module. The
  // CLI's island typing already refused any other unbound name, so what
  // is neither bound nor exported here is a standard global.
  const freeExports = [...idents].filter(
    (id) => !boundVars.has(id) && exports.has(id),
  );
  // Binder classes may never appear in the formula text, but the generated
  // spec must import them to construct instances — every class the nested
  // construction names, not just the binder's own.
  for (const b of binders) {
    if (isClassDomain(b.domain)) collectCtorClasses(b.domain, freeExports);
  }
  const cases = enumerationCases(binders);
  return {
    name: a.propertyName,
    functionName: a.functionName,
    className: a.className,
    isStatic: a.isStatic,
    binders,
    body: loweredBody,
    preconditions,
    freeExports,
    ...(cases !== undefined ? { cases } : {}),
    location: { file, line: a.line },
  };
}

/** Every class named anywhere in a binder's construction tree; the inner
 * ones are constructed by name in the generated file too. */
function collectCtorClasses(domain: ClassCtorDomain, into: string[]): void {
  if (!into.includes(domain.className)) into.push(domain.className);
  /* v8 ignore next -- resolveClassBinders ran first and fills ctorParams at
     every level of the tree, so the empty fallback is unreachable here. */
  for (const p of domain.ctorParams ?? []) {
    if (isClassCtorDomain(p.domain)) collectCtorClasses(p.domain, into);
  }
}
