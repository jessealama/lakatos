/** @ensures{unchanged} forall (x: int ∈ [0, 10)) { bump(x) ≡ x } */
export function bump(x: number): number {
  return x + 1;
}
