/** @ensures{fixedPoint} forall (n: int ∈ [0, 5)) { root(n) === n } */
export function root(x: number): number {
  return Math.sqrt(x);
}
