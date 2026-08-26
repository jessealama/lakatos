/** @ensures{square} forall (n: int ∈ [0, 3)) { square(n) >= 0 } */
export function square(x: number): number {
  return Math.pow(x, 2);
}
