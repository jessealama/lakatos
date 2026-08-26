/** @ensures{picksZero} forall (x: int in [0, 4)) { bit(x) === 0 } */
export function bit(x: number): number {
  if (x === 1 || x === 3) {
    return 0;
  }
  return 1;
}
