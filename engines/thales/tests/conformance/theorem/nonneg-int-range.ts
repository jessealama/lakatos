/** @ensures{grows} forall (x: int ∈ [0, ∞)) { scale(x) >= x } */
export function scale(x: number): number {
  return x * 2;
}
