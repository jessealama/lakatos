/** A ceiling beyond the safe integer range: testing the clamped domain
 * would refute a narrower statement than the one written.
 *
 * @ensures{hugeCeiling} forall (n: int ∈ [0, 1000000000000000000000000000000]) { nonneg(n) }
 * @ensures{ordinary} forall (n: int ∈ [0, 10]) { nonneg(n) }
 */
export function nonneg(n: number): boolean {
  return n >= 0;
}

/** @ensures{hugeFloor} forall (n: int ∈ [-1000000000000000000000000000000, 0]) { nonpos(n) } */
export function nonpos(n: number): boolean {
  return n <= 0;
}

/** @ensures{hugeBoth} forall (n: int ∈ [-1000000000000000000000000000000, 1000000000000000000000000000000]) { anyInt(n) } */
export function anyInt(n: number): boolean {
  return Number.isInteger(n);
}
