import type { Binder, CtorParam } from "./binder.js";
import { bigintBounds, intInterval, isClassDomain } from "./domains.js";

/** How many values a binder ranges over, when that is finite: boolean 2;
 * int, nat, and bigint the size of the denoted interval when both sides
 * are bounded (nat's floor is a bound); undefined for number and string
 * whatever their guard. A class binder counts its constructor's argument
 * tuples, so it is finite exactly when every slot is. */
export function domainCardinality(binder: Binder): bigint | undefined {
  const { domain, range } = binder;
  if (isClassDomain(domain)) return ctorCardinality(domain.ctorParams);
  switch (domain) {
    case "boolean":
      return 2n;
    case "int":
    case "nat": {
      const { lo, hi } = intInterval(domain, range ?? {});
      return lo === undefined || hi === undefined ? undefined : hi - lo + 1n;
    }
    case "bigint": {
      const { lo, hi } = bigintBounds(range ?? {});
      return lo === undefined || hi === undefined ? undefined : hi - lo + 1n;
    }
    case "number":
    case "string":
      return undefined;
  }
}

/** The number of tuples a binder prefix ranges over: the product of the
 * binders' cardinalities, undefined as soon as one is not finite. */
export function prefixCardinality(binders: Binder[]): bigint | undefined {
  let product = 1n;
  for (const b of binders) {
    const n = domainCardinality(b);
    if (n === undefined) return undefined;
    product *= n;
  }
  return product;
}

/** The product over the constructor slots: boolean 2, a class-typed slot
 * its own product, a zero-argument constructor 1; undefined while the
 * class is unresolved or any slot is a number, string, or bigint, which
 * carry no bounds on a constructor parameter. */
function ctorCardinality(params: CtorParam[] | undefined): bigint | undefined {
  if (params === undefined) return undefined;
  let product = 1n;
  for (const p of params) {
    const n =
      p.domain === "boolean"
        ? 2n
        : typeof p.domain === "string"
          ? undefined
          : ctorCardinality(p.domain.ctorParams);
    if (n === undefined) return undefined;
    product *= n;
  }
  return product;
}
