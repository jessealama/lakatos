/** Demonstrates the refuter's reading of a guard that throws: the exception
 * escapes the fc.pre(...) discard and the run reports kind "threw". The
 * prover reads the same guard as a failed `= pure true` hypothesis — the
 * assignment is vacuously satisfied. The divergence is deliberate: an Error
 * verdict can never contradict a Theorem, and each engine's reading is
 * pinned where it lives (this test; the prover's in thales's
 * GuardChainTest).
 *
 * @ensures{guardThrows} forall (x: int) { positive(x) > 0 → positive(x) > 0 }
 */
export function positive(x: number): number {
  if (x < 0) throw new RangeError("negative input");
  return x + 1;
}
