import {
  type ClassCtorDomain,
  type CtorParam,
  isClassCtorDomain,
} from "../../../lemma/src/index.js";
import type { CtorShape } from "./runtime.js";

/** The construction expression for one binder, over the argument tuple
 * `tuple`. JS evaluates arguments left to right and innermost first, so a
 * single try around this call discards the tuple whichever level throws.
 * Shared by the sampled and enumerated emitters so both build instances
 * the same way. */
export function ctorCall(
  cls: string,
  params: CtorParam[],
  tuple: string,
): string {
  if (params.every((p) => !isClassCtorDomain(p.domain))) {
    return `new ${cls}(...${tuple})`;
  }
  const args = params.map((p, i) =>
    isClassCtorDomain(p.domain)
      ? ctorCall(p.domain.className, p.domain.ctorParams!, `${tuple}[${i}]`)
      : `${tuple}[${i}]`,
  );
  return `new ${cls}(${args.join(", ")})`;
}

/** The same tree, for the reporter: it renders the counterexample tuple
 * back as the construction that reproduces the instance. */
export function ctorShape(domain: ClassCtorDomain): CtorShape {
  return {
    className: domain.className,
    params: domain.ctorParams!.map((p) =>
      isClassCtorDomain(p.domain) ? ctorShape(p.domain) : null,
    ),
  };
}
