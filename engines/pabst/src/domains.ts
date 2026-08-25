import {
  anchoredSource,
  bigintBounds,
  type Binder,
  intBounds,
  isClassDomain,
  LemmaError,
  numberConstraints,
  type Primitive,
  regexGuardDomainError,
} from "../../../lemma/src/index.js";

export const DOMAIN_TABLE: Record<Primitive, string> = {
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
  if (isClassDomain(domain)) {
    // Generation draws the constructor's argument tuple; the emitted test
    // runs the real constructor on it (spec/semantics.md).
    if (domain.ctorParams === undefined) {
      throw new LemmaError(
        `unresolved class binder '${domain.className}' reached codegen`,
      );
    }
    const args = domain.ctorParams.map((p) => DOMAIN_TABLE[p.domain]);
    return `fc.tuple(${args.join(", ")})`;
  }
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
      // Every spec reaching here has a representable domain — build-spec
      // refuses the rest — so the clamp these bounds apply is a no-op.
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
      throw new LemmaError(
        `domain '${domain}' does not support interval constraints`,
      );
  }
}

function render(...opts: Array<string | undefined>): string {
  const present = opts.filter((o): o is string => o !== undefined);
  return present.length === 0 ? "()" : `({ ${present.join(", ")} })`;
}
