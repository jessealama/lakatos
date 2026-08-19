/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { sumTo(n) >= 0 } */
export function sumTo(n: number): number {
  let total = 0;
  for (let i = 0; i < n; i++) {
    total += i;
  }
  return total;
}
