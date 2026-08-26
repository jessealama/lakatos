// How both the emitter and its tests read source shapes: SyntaxKind
// names, numeric-literal tokens, binding names, number-binder bounds,
// and the guard-chain shape of a Lemma formula.

import ts from "typescript";
import type { Binder, Formula } from "../../../../lemma/src/index.js";

/** The proper name of each SyntaxKind: plain reverse lookup can land on a
 * First-/Last- range marker sharing the same value, so pick the first
 * non-marker name per value. Every kind has one. */
const KIND_NAMES = new Map<number, string>();
for (const [name, value] of Object.entries(ts.SyntaxKind)) {
  if (
    typeof value === "number" &&
    !/^(First|Last)[A-Z]/.test(name) &&
    !KIND_NAMES.has(value)
  ) {
    KIND_NAMES.set(value, name);
  }
}

export function kindName(kind: ts.SyntaxKind): string {
  return KIND_NAMES.get(kind)!;
}

/** The Lean literal token for a numeric literal. tsc normalizes the
 * literal text (separators stripped, radix prefixes decimalized), and
 * toString prints the shortest round-tripping decimal, which Lean's
 * OfScientific reconstructs as the identical double. */
export function numberToken(lit: ts.NumericLiteral): string {
  const n = Number(lit.text);
  if (!Number.isFinite(n)) return "Infinity";
  return n.toString().replace("e+", "e");
}

/** Every identifier bound by a binding name (destructuring included). */
export function bindingIdentifiers(name: ts.BindingName): ts.Identifier[] {
  if (ts.isIdentifier(name)) return [name];
  const found: ts.Identifier[] = [];
  for (const el of name.elements) {
    if (ts.isBindingElement(el)) found.push(...bindingIdentifiers(el.name));
  }
  return found;
}

/** The comparison a `number` bound lowers to. An interval excludes an endpoint
 * by adjacency in an ordering where -0 sits below 0, which IEEE comparison
 * cannot express: a strict bound at the zero the interval still admits would
 * drop it. Relaxing just those two spellings keeps the prover's domain a
 * superset of the refuter's, which is the safe direction to diverge in. */
function numberBoundOp(
  endpoint: string,
  side: "lower" | "upper",
  open: boolean | undefined,
): "<" | "<=" {
  if (!open) return "<=";
  const v = Number(endpoint);
  // Object.is separates the zeros where === does not.
  const relax = side === "lower" ? Object.is(v, -0) : Object.is(v, 0);
  return relax ? "<=" : "<";
}

/** One side of the bound a `number` binder lowers to: the comparison and
 * the endpoint literal it reads against the bound variable. */
export interface FloatBound {
  op: "<" | "<=";
  /** The endpoint as the literal the emitted bound carries. */
  lit: string;
}

/** One side of the guard a `number` binder lowers to. */
export interface GuardBound extends FloatBound {
  /** The endpoint as a double, on the side the comparison reads it:
   * `lo.op` compares `lo.val` against the bound variable, `hi.op` the
   * variable against `hi.val`. */
  val: number;
}

/** The bounds a `number` binder's interval lowers to — the single authority
 * both pipelines read. An interval bounds both of its sides: an ∞ endpoint
 * bounds against the literal infinity — strictly when open, so that sign's
 * infinity is excluded, non-strictly when closed, which IEEE comparison
 * still refuses for NaN. That makes any interval NaN-free, matching the
 * refuter's unconditional noNaN. Only a binder with no interval at all is
 * unbounded, and it quantifies over every double. */
export function numberBounds(range: Binder["range"]): {
  lower?: FloatBound;
  upper?: FloatBound;
} {
  if (range === undefined) return {};
  const lower: FloatBound =
    range.min !== undefined
      ? {
          op: numberBoundOp(range.min, "lower", range.minOpen),
          lit: range.min,
        }
      : { op: range.minOpen ? "<" : "<=", lit: "-Infinity" };
  const upper: FloatBound =
    range.max !== undefined
      ? {
          op: numberBoundOp(range.max, "upper", range.maxOpen),
          lit: range.max,
        }
      : { op: range.maxOpen ? "<" : "<=", lit: "Infinity" };
  return { lower, upper };
}

/** The guard a `number` binder's interval lowers to, as comparisons rather
 * than as DSL text — `numberBounds` with each endpoint's double alongside
 * it. Reporting the guard this way is what lets a test pin the two engines'
 * domains against each other. */
export function numberGuard(range: Binder["range"]): {
  lo?: GuardBound;
  hi?: GuardBound;
} {
  const { lower, upper } = numberBounds(range);
  if (lower === undefined || upper === undefined) return {};
  return {
    lo: { op: lower.op, val: Number(lower.lit), lit: lower.lit },
    hi: { op: upper.op, val: Number(upper.lit), lit: upper.lit },
  };
}

/** The body shapes this slice can structure, as guard atoms around a
 * conclusion atom: a bare atom, or a top-level implication chain whose
 * antecedents and conclusion are all atoms — exactly the shape the refuter
 * lowers to fc.pre discards. Any other connective is undefined (bare). */
export function chainReading(
  ast: Formula,
): { guards: string[]; conclusion: string } | undefined {
  if (ast.kind === "atom") return { guards: [], conclusion: ast.js };
  if (ast.kind !== "implication") return undefined;
  if (ast.consequent.kind !== "atom") return undefined;
  const guards: string[] = [];
  for (const a of ast.antecedents) {
    if (a.kind !== "atom") return undefined;
    guards.push(a.js);
  }
  return { guards, conclusion: ast.consequent.js };
}
