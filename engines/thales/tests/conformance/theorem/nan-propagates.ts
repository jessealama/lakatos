/** @ensures{propagates} forall (n: int ∈ [0, 4)) { Object.is(addNaN(n), NaN) } */
export function addNaN(x: number): number {
  return x + NaN;
}
