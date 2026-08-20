/** @ensures{nonneg} forall (x: int ∈ [0, 1000000000000000000000000000000]) { keep(x) >= 0 } */
export function keep(x: number): number {
  return x;
}
