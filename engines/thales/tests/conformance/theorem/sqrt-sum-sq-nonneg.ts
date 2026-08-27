/** @ensures{nonNeg} forall (x: number in [-10, 10]) { root(x) >= 0 } */
export function root(x: number): number {
  return Math.sqrt(x * x);
}
