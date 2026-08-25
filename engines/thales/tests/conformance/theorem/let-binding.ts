/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { shifted(n) >= 0 } */
export function shifted(n: number): number {
  let total = n + 1;
  return total + 1;
}
