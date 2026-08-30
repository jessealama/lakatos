/** @ensures{mixed} forall (n: int ∈ [0, 3)) { Object.is(Number.isFinite(n), n) } */
export function probe(n: number): number {
  return n;
}
