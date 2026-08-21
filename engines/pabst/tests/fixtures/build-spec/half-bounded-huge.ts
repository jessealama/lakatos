/** Unbounded below, huge ceiling. The prover degrades this to its bare
 * command and proves over all of Int — a superset of what was written —
 * while the refuter refuses. Both diverge in the safe direction: neither
 * ever works over a domain narrower than the annotation says.
 *
 * @ensures{ceiling} forall (n: int ∈ (-∞, 1000000000000000000000000000000]) { below(n) }
 */
export function below(n: number): boolean {
  return Number.isInteger(n);
}
