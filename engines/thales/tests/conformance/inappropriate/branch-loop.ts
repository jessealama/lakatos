/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { countDown(n) >= 0 } */
export function countDown(n: number): number {
  let total = n;
  if (n > 0) {
    while (total > 0) {
      total = total - 1;
    }
  }
  return total;
}
