/** @ensures{commutes} forall (x: int) (y: int) { mul(x, y) ≡ mul(y, x) } */
export function mul(x: number, y: number): number {
  return x * y;
}
