/** @ensures{positive} forall (x: int ∈ [0, 10]) { x > 0 → reciprocal(x) > 0 } */
export function reciprocal(x: number): number {
  if (x === 0) {
    throw new RangeError(`cannot invert ${x}`);
  }
  return 1 / x;
}
