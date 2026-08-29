import { type Binder, type CtorParam, isClassCtorDomain } from "./binder.js";
import { isClassDomain } from "./domains.js";
import { LemmaError } from "./errors.js";

/** What resolution needs to know about one named class declaration. */
export interface ClassInfo {
  exported: boolean;
  defaultExport: boolean;
  /** Present when every constructor parameter is generable. */
  ctorParams?: CtorParam[];
  /** Why the constructor cannot be generated for, naming the offender. */
  ctorProblem?: string;
}

export type ClassTable = Map<string, ClassInfo>;

/**
 * Resolve each class-domain binder against the annotated module: the name
 * must denote an exported, non-default class whose constructor parameters
 * are all generable (spec/semantics.md, "Class-valued binders"). Attaches
 * the constructor parameters to the binder's domain; throws LemmaError on
 * the first binder that fails.
 */
export function resolveClassBinders(
  binders: Binder[],
  classes: ClassTable,
  file: string,
): void {
  for (const b of binders) {
    if (!isClassDomain(b.domain)) continue;
    b.domain.ctorParams = resolveClass(b.domain.className, classes, file, []);
  }
}

/**
 * The constructor parameters of `name`, with every class-typed parameter
 * resolved in turn, so the returned tree bottoms out in primitives. `path`
 * is the chain of enclosing classes, which makes a cycle visible before the
 * recursion could follow it.
 */
function resolveClass(
  name: string,
  classes: ClassTable,
  file: string,
  path: string[],
): CtorParam[] {
  const info = classes.get(name);
  if (info === undefined) {
    throw new LemmaError(
      `domain '${name}' is neither a primitive domain ` +
        `(int, nat, number, boolean, string, bigint) ` +
        `nor an exported class declared in ${file}`,
    );
  }
  if (info.defaultExport) {
    throw new LemmaError(
      `class '${name}' is default-exported from ${file}; ` +
        `a binder domain needs a named export`,
    );
  }
  if (!info.exported) {
    throw new LemmaError(
      `class '${name}' is not exported from ${file}, ` +
        `so no caller outside the module can construct one`,
    );
  }
  if (info.ctorParams === undefined) {
    throw new LemmaError(
      `class '${name}' cannot be generated: ${info.ctorProblem}`,
    );
  }
  const params = info.ctorParams;
  for (const p of params) {
    if (!isClassCtorDomain(p.domain)) continue;
    const inner = p.domain.className;
    const at = path.indexOf(inner);
    const chain = at >= 0 ? path.slice(at) : inner === name ? [] : undefined;
    if (chain !== undefined) {
      throw new LemmaError(
        `class '${name}' cannot be generated: constructor parameter ` +
          `'${p.name}' closes the cycle ${[...chain, name, inner].join(" → ")} — ` +
          `a cyclic constructor-parameter graph has no base case`,
      );
    }
    p.domain.ctorParams = resolveClass(inner, classes, file, [...path, name]);
  }
  return params;
}
