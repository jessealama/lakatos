/** @ensures{neverNull} forall (x: number) { Object.is(nullFlag(x), 0) } */
export function nullFlag(v: number | null): number {
  if (Object.is(v, null)) {
    return 1;
  }
  return 0;
}
