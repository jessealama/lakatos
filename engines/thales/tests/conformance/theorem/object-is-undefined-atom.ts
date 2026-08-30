/** @ensures{neverUndefined} forall (x: number) { definedOnly(x) === 1 } */
export function definedOnly(x: number): number {
  if (Object.is(x, undefined)) {
    return 0;
  }
  return 1;
}
