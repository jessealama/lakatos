/** @ensures{nonNegative} forall (n: int ∈ [0, 4)) { addNaN(n) >= 0 } */
export function addNaN(x: number): number {
  return x + NaN;
}
