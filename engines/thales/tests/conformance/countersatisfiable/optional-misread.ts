/** @ensures{absentIsArgument} forall (x: int ∈ [0, 4)) { Object.is(pick(), x) } */
export function pick(y?: number): number {
  if (y === undefined) {
    return 0;
  }
  return y;
}
