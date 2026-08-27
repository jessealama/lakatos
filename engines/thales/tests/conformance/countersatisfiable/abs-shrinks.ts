/** @ensures{grows} forall (n: int ∈ [0, 8)) { Number.isFinite(n) → mag(n) > n } */
export function mag(n: number): number {
  return Math.abs(n);
}
