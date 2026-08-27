/** @ensures{nonNeg} forall (n: int ∈ [0, 8)) { Number.isFinite(n) → scale(n) >= 0 } */
export function scale(n: number): number {
  return Math.abs(n) * 2;
}
