/** @ensures{doubles} forall (x: int) { dbl(x) ≡ x + x } */
export function dbl(x: number): number {
  return x * 2;
}
