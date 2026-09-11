/** @ensures{exactPastTwo24} forall (n: int ∈ [16777216, 16777218)) { narrow(n) ≡ n } */
export function narrow(x: number): number {
  return Math.fround(x);
}
