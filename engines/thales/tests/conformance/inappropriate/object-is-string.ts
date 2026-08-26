/** @ensures{mixed} forall (x: number) { pick(x) === 1 } */
export function pick(x: number): number {
  if (Object.is(x, "zero")) {
    return 0;
  }
  return 1;
}
