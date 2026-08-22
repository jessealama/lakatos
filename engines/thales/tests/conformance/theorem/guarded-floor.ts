/** @ensures{guardedFloor} forall (x: int ∈ [0, 10)) { x >= 1 → keep(x) >= 1 } */
export function keep(x: number): number {
  return x;
}
