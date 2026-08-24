/**
 * @ensures{monotone} forall (x y: number) (sf: number ∈ (0, 1000)) {
 *   x <= y → scaleBounded(x, sf) <= scaleBounded(y, sf)
 * }
 */
export function scaleBounded(value: number, sourceFactor: number): number {
  return value * sourceFactor;
}

/**
 * @ensures{monotone} forall (x y: number) (c: number ∈ [-100, 100]) {
 *   x <= y → shiftBounded(x, c) <= shiftBounded(y, c)
 * }
 */
export function shiftBounded(value: number, offset: number): number {
  return value + offset;
}
