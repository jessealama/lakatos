import type { DoubleConstraints } from "fast-check";
import type { Binder, Domain, Range } from "./binder.js";

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

/** The one rendering of the ±MAX_SAFE limit diagnostics may use. */
export const SAFE_INTEGER_RANGE = `the safe integer range (±${MAX_SAFE})`;

export interface IntBounds {
  lo: bigint;
  hi: bigint;
  /** The corresponding finite endpoint fell outside the safe integer
   * range, so the interval was intersected with it (possibly to
   * emptiness: lo > hi). The nat floor is not clamping. */
  clampedLo: boolean;
  clampedHi: boolean;
  /** The bounds before the safe-range intersection (open endpoints folded,
   * nat floored): rawLo <= rawHi with lo > hi means the clamp alone
   * emptied the interval. */
  rawLo: bigint;
  rawHi: bigint;
}

/** An int/nat interval as mathematics, not as any generator sees it: an
 * absent side is genuinely unbounded, never a stand-in limit. */
export interface IntInterval {
  lo?: bigint;
  hi?: bigint;
}

/** The exact set of integers an int/nat interval denotes: open endpoints
 * fold into ±1 and nat floors at 0 (so nat's lower side is always
 * bounded), with no safe-range intersection. The normalization every
 * consumer shares, so equivalent domains cannot be treated differently. */
export function intInterval(domain: "int" | "nat", range: Range): IntInterval {
  const interval: IntInterval = {};
  if (range.min !== undefined) {
    interval.lo = BigInt(range.min) + (range.minOpen ? 1n : 0n);
  }
  if (range.max !== undefined) {
    interval.hi = BigInt(range.max) - (range.maxOpen ? 1n : 0n);
  }
  if (domain === "nat" && (interval.lo === undefined || interval.lo < 0n)) {
    interval.lo = 0n;
  }
  return interval;
}

/** The inclusive fc.integer bounds an int/nat interval lowers to: the
 * denoted interval, intersected with the safe integer range. Both sides
 * are always concrete — fc.integer's implicit defaults are 32-bit, so a
 * far-out explicit bound with an omitted side would crash it — and an
 * unbounded (∞) side means the safe-range limit. */
export function intBounds(domain: "int" | "nat", range: Range): IntBounds {
  const denoted = intInterval(domain, range);
  let lo = denoted.lo ?? -MAX_SAFE;
  let hi = denoted.hi ?? MAX_SAFE;
  const rawLo = lo;
  const rawHi = hi;
  const clampedLo = lo < -MAX_SAFE || lo > MAX_SAFE;
  const clampedHi = hi < -MAX_SAFE || hi > MAX_SAFE;
  if (lo < -MAX_SAFE) lo = -MAX_SAFE;
  if (hi > MAX_SAFE) hi = MAX_SAFE;
  return { lo, hi, clampedLo, clampedHi, rawLo, rawHi };
}

/** The finite endpoints of a binder's interval that fall outside the safe
 * integer range, as the user wrote them; empty when the domain is
 * representable as written. Both engines refuse on this one answer rather
 * than substituting the clamped domain, which denotes a narrower statement. */
export function clampedEndpoints(binder: Binder): string[] {
  const { domain, range } = binder;
  if (range === undefined) return [];
  if (domain !== "int" && domain !== "nat") return [];
  const { clampedLo, clampedHi } = intBounds(domain, range);
  return [
    ...(clampedLo ? [range.min!] : []),
    ...(clampedHi ? [range.max!] : []),
  ];
}

/** The one rendering of why a clamped domain was not attempted. */
export function unsupportedRangeReason(endpoints: string[]): string {
  const one = endpoints.length === 1;
  return (
    `endpoint${one ? "" : "s"} ${endpoints.join(" and ")} ` +
    `exceed${one ? "s" : ""} ${SAFE_INTEGER_RANGE}`
  );
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

/** The fast-check constraints the refuter generates a `number` binder from.
 * The one construction both the emitted `fc.double(...)` text and any direct
 * caller derive from, so what the refuter samples cannot drift from what a
 * consumer checks against. */
export function numberDoubleConstraints(range: Range): DoubleConstraints {
  const c = numberConstraints(range);
  const opts: DoubleConstraints = {
    noNaN: true,
    minExcluded: c.minExcluded,
    maxExcluded: c.maxExcluded,
  };
  if (c.min) opts.min = c.min.val;
  if (c.max) opts.max = c.max.val;
  return opts;
}
