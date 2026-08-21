/** Empty within the safe range: bad input, not an unrepresentable domain.
 *
 * @ensures{backwards} forall (n: int ∈ [5, 3]) { small(n) }
 */
export function small(n: number): boolean {
  return n > 0;
}
