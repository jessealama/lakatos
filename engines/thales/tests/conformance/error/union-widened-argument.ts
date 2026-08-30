export function wide(v: number | string | boolean): number {
  return 0;
}

/** @ensures{p} forall (x: number) { Object.is(narrow(x), 0) } */
export function narrow(v: number | string): number {
  return wide(v);
}
