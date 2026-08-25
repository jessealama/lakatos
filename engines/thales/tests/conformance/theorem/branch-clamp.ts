/** @ensures{nonNegative} forall (x: number ∈ (-∞, ∞)) { clamp(x) >= 0 } */
export function clamp(x: number): number {
  if (x < 0) {
    return 0;
  }
  return x;
}
