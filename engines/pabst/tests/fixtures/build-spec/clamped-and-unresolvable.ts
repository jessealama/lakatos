/** Clamped and otherwise untestable: the second blocker keeps its own
 * diagnostic, so the clamp is not what gets reported.
 *
 * @ensures{both} forall (n: int ∈ [0, 1000000000000000000000000000000]) { nowhere(n) }
 */
export function present(n: number): boolean {
  return n >= 0;
}
