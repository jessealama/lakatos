const EPSILON = Number.EPSILON;

/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { nudge(n) >= 0 } */
export function nudge(x: number): number {
  return x + EPSILON;
}
