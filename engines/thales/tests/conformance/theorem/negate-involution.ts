/**
 * @ensures{involutive} forall (x: int ∈ [-10, 10)) { negate(negate(x)) ≡ x }
 * @ensures{involutiveEverywhere} forall (x: int) { negate(negate(x)) ≡ x }
 */
export function negate(x: number): number {
  return -x;
}
