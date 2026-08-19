/** @ensures{commutes} forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) } */
export function add(a: number, b: number): number {
  return a + b;
}
