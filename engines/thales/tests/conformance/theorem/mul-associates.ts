/** @ensures{associates} forall (a: int ∈ [0, 6)) (b: int ∈ [0, 6)) (c: int ∈ [0, 6)) { mul(mul(a, b), c) ≡ mul(a, mul(b, c)) } */
export function mul(a: number, b: number): number {
  return a * b;
}
