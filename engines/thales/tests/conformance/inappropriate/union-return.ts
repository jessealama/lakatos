/** @ensures{p} forall (x: number) { Object.is(echo(x), x) } */
export function echo(v: number | string): number | string {
  return v;
}
