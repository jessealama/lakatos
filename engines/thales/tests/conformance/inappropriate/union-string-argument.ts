/** @ensures{p} forall (x: number) { Object.is(toNum("x"), 0) } */
export function toNum(v: number | string): number {
  if (typeof v === "number") {
    return v;
  }
  return 0;
}
