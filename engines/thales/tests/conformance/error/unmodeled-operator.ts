/** @ensures{stuck} forall (x: int ∈ [0, 5)) { masked(x) ≡ x } */
export function masked(x: number): number {
  return x & 7;
}
