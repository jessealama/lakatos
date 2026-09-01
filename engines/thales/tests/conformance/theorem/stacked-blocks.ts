/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { keep(n) >= 0 } */
/** @ensures{atLeastOne} forall (n: int ∈ [0, 10)) { keep(n) >= 1 } */
export function keep(n: number): number {
  return n + 1;
}
