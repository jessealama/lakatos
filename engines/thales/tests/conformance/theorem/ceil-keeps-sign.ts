/** @ensures{negativeZero} forall (n: int ∈ [1, 10)) { Object.is(dampen(n), -0) } */
export function dampen(x: number): number {
  return Math.ceil(-x / 10);
}
