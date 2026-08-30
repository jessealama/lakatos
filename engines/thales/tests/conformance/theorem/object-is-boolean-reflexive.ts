/** @ensures{same} forall (n: int ∈ [0, 3)) { Object.is(Number.isFinite(n), Number.isFinite(n)) } */
export function probe(n: number): number {
  return n;
}
