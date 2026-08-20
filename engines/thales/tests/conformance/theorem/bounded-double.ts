/** @ensures{doubling} forall (x: int ∈ [0, 20000)) { dbl(x) === x + x } */
export function dbl(x: number): number {
  return x * 2;
}
