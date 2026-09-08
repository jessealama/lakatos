/** @ensures{nonNegative} forall (d: int ∈ [0, 100)) { daysToWeeks(d) >= 0 } */
export function daysToWeeks(days: number): number {
  return Math.trunc(days / 7);
}
