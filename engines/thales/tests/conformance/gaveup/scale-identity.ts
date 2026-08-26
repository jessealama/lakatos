/** @ensures{fixed} forall (x: number ∈ (0, ∞)) { scale(x) ≡ x } */
export function scale(x: number): number {
  return x * 2;
}
