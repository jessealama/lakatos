/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { root(n) >= 0 } */
export function root(x: number): number {
  const sqrt = Math.sqrt;
  return sqrt(x);
}
