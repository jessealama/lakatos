/** @ensures{notBig} forall (n: int in [0, 3)) { ¬(bump(n) > 100) } */
/** @ensures{both} forall (n: int in [0, 3)) { bump(n) > n ∧ bump(n) > 0 } */
/** @ensures{nested} forall (n: int in [0, 3)) { ¬(bump(n) === 0 ∨ bump(n) > 3) ∧ bump(n) >= 1 } */
export function bump(n: number): number {
  return n + 1;
}
