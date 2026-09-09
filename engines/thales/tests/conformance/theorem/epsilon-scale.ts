/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { tiny(n) >= 0 } */
export function tiny(x: number): number {
  return x * Number.EPSILON;
}
