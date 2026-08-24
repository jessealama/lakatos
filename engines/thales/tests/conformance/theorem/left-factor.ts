/**
 * @ensures{monotone} forall (x y: number) (sf: number ∈ (0, ∞)) {
 *   x <= y → scale(x, sf) <= scale(y, sf)
 * }
 */
export function scale(value: number, sourceFactor: number): number {
  return sourceFactor * value;
}

/**
 * @ensures{monotone} forall (x y: number) (c: number ∈ (-∞, ∞)) {
 *   x <= y → shift(x, c) <= shift(y, c)
 * }
 */
export function shift(value: number, offset: number): number {
  return offset + value;
}
