/** @ensures{vanishes} forall (n: int ∈ [0, 10)) { shrink(n) === 0 } */
export function shrink(x: number): number {
  return x / Number.POSITIVE_INFINITY;
}
