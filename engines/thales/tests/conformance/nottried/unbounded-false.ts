/** @ensures{unchanged} forall (x: int) { bump(x) ≡ x } */
export function bump(x: number): number {
  return x + 1;
}
