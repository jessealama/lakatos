/** @ensures{numId} forall (x: number) { Object.is(toNum(x), x) } */
export function toNum(v: number | string): number {
  if (typeof v === "number") {
    return v;
  }
  return 0;
}

/** @ensures{nullNeverHits} forall (x: number) { Object.is(nullFlag(x), 0) } */
export function nullFlag(v: number | null): number {
  if (Object.is(v, null)) {
    return 1;
  }
  return 0;
}

/** @ensures{passthrough} forall (x: int ∈ [0, 4)) { Object.is(relay(x), x) } */
export function relay(v: number | string): number {
  return toNum(v);
}
