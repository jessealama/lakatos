/** @ensures{alwaysOne} forall (x: number) { pick(x) === 1 } */
export function pick(x: number): number {
  if (Object.is(Number.isFinite(x), x)) {
    return 0;
  }
  return 1;
}
