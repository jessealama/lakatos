/** @ensures{nonneg} forall (x: int ∈ [0, 1000000)) { sq(x) >= 0 } */
export function sq(x: number): number {
  return x * x;
}
