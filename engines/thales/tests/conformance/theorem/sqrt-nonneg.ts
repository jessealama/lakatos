/** @ensures{nonNegative} forall (n: int ∈ [0, 5)) { root(n) >= 0 } */
export function root(x: number): number {
  return Math.sqrt(x);
}
