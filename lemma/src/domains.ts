import type { Domain, Range } from "./binder.js";

// A Record rather than a list so adding a Domain member without updating
// this table is a type error.
const DOMAINS: Record<Domain, true> = {
  int: true,
  nat: true,
  number: true,
  boolean: true,
  string: true,
  bigint: true,
};

export function isDomain(s: string): s is Domain {
  return Object.prototype.hasOwnProperty.call(DOMAINS, s);
}

export const MAX_SAFE = 9007199254740991n;

export interface IntBounds {
  lo: bigint;
  hi: bigint;
  /** A finite endpoint fell outside the safe integer range, so the
   * interval was intersected with it (possibly to emptiness: lo > hi). */
  clamped: boolean;
}

/** The inclusive fc.integer bounds an int/nat interval lowers to: open
 * endpoints fold into ±1 (fc.integer has no exclusion options), nat floors
 * at 0, and the result is intersected with the safe integer range. Both
 * sides are always concrete — fc.integer's implicit defaults are 32-bit,
 * so a far-out explicit bound with an omitted side would crash it — and an
 * unbounded (∞) side means the safe-range limit. */
export function intBounds(domain: "int" | "nat", range: Range): IntBounds {
  let lo =
    range.min === undefined
      ? -MAX_SAFE
      : BigInt(range.min) + (range.minOpen ? 1n : 0n);
  let hi =
    range.max === undefined
      ? MAX_SAFE
      : BigInt(range.max) - (range.maxOpen ? 1n : 0n);
  if (domain === "nat" && lo < 0n) lo = 0n;
  const clamped =
    lo < -MAX_SAFE || lo > MAX_SAFE || hi < -MAX_SAFE || hi > MAX_SAFE;
  if (lo < -MAX_SAFE) lo = -MAX_SAFE;
  if (hi > MAX_SAFE) hi = MAX_SAFE;
  return { lo, hi, clamped };
}

/** The inclusive fc.bigInt bounds a bigint interval lowers to. An
 * unbounded side stays undefined — fc.bigInt, unlike fc.integer, widens
 * its default range around a far-out explicit bound. */
export function bigintBounds(range: Range): { lo?: bigint; hi?: bigint } {
  const lo =
    range.min === undefined
      ? undefined
      : BigInt(range.min) + (range.minOpen ? 1n : 0n);
  const hi =
    range.max === undefined
      ? undefined
      : BigInt(range.max) - (range.maxOpen ? 1n : 0n);
  const bounds: { lo?: bigint; hi?: bigint } = {};
  if (lo !== undefined) bounds.lo = lo;
  if (hi !== undefined) bounds.hi = hi;
  return bounds;
}

/** One endpoint of a number interval as fc.double sees it: the literal
 * text emitted into the generated test, and its numeric value (used to
 * validate the constraints with fc itself at parse time). */
export interface NumberBound {
  lit: string;
  val: number;
}

export interface NumberConstraints {
  min?: NumberBound;
  minExcluded: boolean;
  max?: NumberBound;
  maxExcluded: boolean;
}

/** The fc.double constraints a number interval lowers to. An open ∞
 * endpoint becomes an excluded infinite bound, which fast-check clamps to
 * ±MAX_VALUE; a closed ∞ endpoint is fc.double's default (inclusive ±∞),
 * so that side is simply omitted. */
export function numberConstraints(range: Range): NumberConstraints {
  const c: NumberConstraints = {
    minExcluded: range.minOpen === true,
    maxExcluded: range.maxOpen === true,
  };
  if (range.min !== undefined) {
    c.min = { lit: range.min, val: Number(range.min) };
  } else if (range.minOpen) {
    c.min = { lit: "Number.NEGATIVE_INFINITY", val: Number.NEGATIVE_INFINITY };
  }
  if (range.max !== undefined) {
    c.max = { lit: range.max, val: Number(range.max) };
  } else if (range.maxOpen) {
    c.max = { lit: "Number.POSITIVE_INFINITY", val: Number.POSITIVE_INFINITY };
  }
  return c;
}
