/** @ensures{numId} forall (x: number) { Object.is(toNum(x), x) } */
export function toNum(v: number | string): number {
  if (typeof v === "number") {
    return v;
  }
  return 0;
}
