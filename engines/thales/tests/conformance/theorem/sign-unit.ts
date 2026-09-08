/** @ensures{atMostOne} forall (n: int ∈ [-3, 3)) { signOf(n) <= 1 } */
/** @ensures{atLeastMinusOne} forall (n: int ∈ [-3, 3)) { signOf(n) >= -1 } */
export function signOf(x: number): number {
  return Math.sign(x);
}
