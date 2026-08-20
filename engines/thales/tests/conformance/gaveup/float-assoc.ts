/** @ensures{assoc} forall (a: int ∈ [9007199254740990, 9007199254740991]) (b: int ∈ [2, 2]) (c: int ∈ [1, 1]) { assoc3(a, b, c) ≡ a + (b + c) } */
export function assoc3(a: number, b: number, c: number): number {
  return (a + b) + c;
}
