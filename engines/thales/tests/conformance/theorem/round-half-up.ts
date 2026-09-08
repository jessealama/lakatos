/** @ensures{tieRoundsUp} forall (n: int ∈ [0, 100)) { 2 * roundHalf(n) >= n } */
export function roundHalf(n: number): number {
  return Math.round(n / 2);
}
