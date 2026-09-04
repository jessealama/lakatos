/** @ensures{pos} forall (n: int ∈ [1, 10]) { square(n) > 0 } */
export function square(n: number): number {
  return n * n;
}
