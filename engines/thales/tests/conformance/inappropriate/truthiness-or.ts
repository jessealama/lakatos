/** @ensures{p} forall (x: int in [0, 4)) { pick(x) >= 0 } */
export function pick(x: number): number {
  if (x || 1) {
    return 0;
  }
  return 1;
}
