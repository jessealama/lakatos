let factor = 2;

/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { scale(n) >= 0 } */
export function scale(n: number): number {
  return n * factor;
}
