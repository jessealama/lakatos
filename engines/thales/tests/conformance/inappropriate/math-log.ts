/** @ensures{nonNegative} forall (n: int ∈ [1, 100)) { integerLog(n) >= 0 } */
export function integerLog(n: number): number {
  return Math.log(n);
}
