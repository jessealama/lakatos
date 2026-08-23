/**
 * @ensures{belowDivisor} forall (x: int ∈ [0, 100)) { rem(x, 7) < 7 }
 * @ensures{dividendSign} forall (x: int ∈ [-100, 0)) { rem(x, 7) <= 0 }
 */
export function rem(a: number, b: number): number {
  return a % b;
}
