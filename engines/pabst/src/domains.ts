import type { Binder, Domain } from "../../../lemma/src/binder.js";
import {
  bigintBounds,
  intBounds,
  numberConstraints,
} from "../../../lemma/src/domains.js";
import {
  anchoredSource,
  regexGuardDomainError,
} from "../../../lemma/src/regex-guard.js";
import { PabstError } from "./errors.js";

export const DOMAIN_TABLE: Record<Domain, string> = {
  int: "fc.integer()",
  nat: "fc.nat()",
  number: "fc.double()",
  boolean: "fc.boolean()",
  string: "fc.string()",
  bigint: "fc.bigInt()",
};

/** The binder's guards are mutually exclusive per domain, so arbitraryFor
 * takes the binder itself rather than growing a positional parameter per
 * guard kind. */
export function arbitraryFor(
  binder: Pick<Binder, "domain" | "range" | "pattern">,
): string {
  const { domain, range, pattern } = binder;
  if (pattern) {
    if (domain !== "string") {
      // Unreachable via the parser (parseRegexGuard rejects these), kept
      // as a backstop for direct callers.
      throw regexGuardDomainError(domain);
    }
    // Safe to re-emit as a literal: the source came from a literal scan,
    // so any '/' in it is escaped or inside a character class.
    return `fc.stringMatching(/${anchoredSource(pattern.source)}/${pattern.flags})`;
  }
  if (!range) return DOMAIN_TABLE[domain];
  switch (domain) {
    case "int":
    case "nat": {
      // A ranged nat is just a bounded integer; fc.nat has no `min`.
      const { lo, hi } = intBounds(domain, range);
      return `fc.integer({ min: ${lo}, max: ${hi} })`;
    }
    case "number": {
      // Bounded fc.double still generates NaN unless told otherwise, and
      // NaN satisfies no interval.
      const c = numberConstraints(range);
      const opts: string[] = [];
      if (c.min) opts.push(`min: ${c.min.lit}`);
      if (c.minExcluded) opts.push(`minExcluded: true`);
      if (c.max) opts.push(`max: ${c.max.lit}`);
      if (c.maxExcluded) opts.push(`maxExcluded: true`);
      opts.push(`noNaN: true`);
      return `fc.double({ ${opts.join(", ")} })`;
    }
    case "bigint": {
      const { lo, hi } = bigintBounds(range);
      return `fc.bigInt${render(
        lo === undefined ? undefined : `min: ${lo}n`,
        hi === undefined ? undefined : `max: ${hi}n`,
      )}`;
    }
    default:
      // Unreachable via the parser (parseRange rejects these), kept as a
      // backstop for direct callers.
      throw new PabstError(
        `domain '${domain}' does not support interval constraints`,
      );
  }
}

function render(...opts: Array<string | undefined>): string {
  const present = opts.filter((o): o is string => o !== undefined);
  return present.length === 0 ? "()" : `({ ${present.join(", ")} })`;
}
