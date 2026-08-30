/**
 * @ensures{absentIsZero} forall (x: int ∈ [0, 4)) { Object.is(pick() + x, x) }
 * @ensures{presentIsArgument} forall (x: number) { Object.is(pick(x), x) }
 */
export function pick(y?: number): number {
  if (y === undefined) {
    return 0;
  }
  return y;
}
