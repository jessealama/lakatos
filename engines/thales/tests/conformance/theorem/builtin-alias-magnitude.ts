const safeMathAbs = Math.abs;

/** @ensures{nonNegative} forall (n: int ∈ [-10, 10)) { magnitude(n) >= 0 } */
export function magnitude(n: number): number {
  return safeMathAbs(n);
}
