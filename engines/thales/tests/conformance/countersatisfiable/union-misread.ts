/** @ensures{misreads} forall (x: int ∈ [0, 4)) { Object.is(toNum(x), x + 1) } */
export function toNum(v: number | string): number {
  if (typeof v === "number") {
    return v;
  }
  return 0;
}
