/** Every tuple is discarded by the antecedent; walking all ten is still a
 * Theorem, with the full case count.
 *
 * @ensures{vacuous} forall (n: int ∈ [1, 10]) { n > 10 → never(n) }
 */
export function never(n: number): boolean {
  return n < 0;
}
