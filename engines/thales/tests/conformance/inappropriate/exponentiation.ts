/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { square(x) >= 0 } */
export function square(x: number): number {
  return x ** 2;
}
