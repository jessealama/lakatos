/** @ensures{p} forall (x: int ∈ [0, 4)) { Object.is(span(x), x) } */
export function span(lo?: number, hi: number): number {
  return hi;
}
