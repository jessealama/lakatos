/** Nonempty as written, emptied by the clamp alone: no domain is left to
 * generate over, so there is nothing to refute.
 *
 * @ensures{emptied} forall (n: int ∈ [1000000000000000000000000000000, 10000000000000000000000000000000]) { huge(n) }
 */
export function huge(n: number): boolean {
  return n > 0;
}
