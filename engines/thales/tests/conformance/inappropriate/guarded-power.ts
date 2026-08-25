// The refusal is in the guard, not the conclusion: the whole formula is
// outside the model, so no annotation reaches the prover.
/** @ensures{guardedPower} forall (x: int ∈ [0, 10)) { x ** 2 >= 0 → keep(x) >= 0 } */
export function keep(x: number): number {
  return x;
}
