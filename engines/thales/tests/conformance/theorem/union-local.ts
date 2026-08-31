/** @ensures{numId} forall (x: number) { Object.is(carry(x), x) } */
export function carry(v: number | string): number {
  const w: number | string = v;
  if (typeof w === "number") {
    return w;
  }
  return 0;
}
