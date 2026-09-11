/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { narrow(n) >= 0 } */
/** @ensures{exactOnSmallIntegers} forall (n: int ∈ [0, 10)) { narrow(n) ≡ n } */
export function narrow(x: number): number {
  return Math.fround(x);
}
