/** Fails at (0, 3), (1, 2), (2, 1), and (3, 0); the walk is ascending in
 * a then b, so the reported tuple is (0, 3).
 *
 * @ensures{noThree} forall (a: int ∈ [0, 3]) (b: int ∈ [0, 3]) { sum(a, b) !== 3 }
 */
export function sum(a: number, b: number): number {
  return a + b;
}

/** Throws at the least value first.
 *
 * @ensures{rootDefined} forall (n: int ∈ [-2, 2]) { root(n) >= 0 }
 */
export function root(n: number): number {
  if (n < 0) throw new RangeError(`negative: ${n}`);
  return Math.sqrt(n);
}
