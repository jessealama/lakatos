/**
 * @ensures{monotone} forall (x y: number)
 *   (sf: number ∈ (0, ∞)) (so: number ∈ (-∞, ∞))
 *   (tf: number ∈ (0, ∞)) (to: number ∈ (-∞, ∞)) {
 *   x <= y → applyConversionFactors(x, sf, so, tf, to) <= applyConversionFactors(y, sf, so, tf, to)
 * }
 */
export function applyConversionFactors(
  value: number,
  sourceFactor: number,
  sourceOffset: number,
  targetFactor: number,
  targetOffset: number,
): number {
  const baseValue = value * sourceFactor + sourceOffset;
  return (baseValue - targetOffset) / targetFactor;
}
