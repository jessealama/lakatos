/** @ensures{commutes} forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { f(a, b) ≡ f(b, a) } */
export function f(a: number, b: number): number {
  return a + a;
}
