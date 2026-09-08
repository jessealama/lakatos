/** @ensures{integral} forall (n: int ∈ [0, 10)) { Number.isInteger(triple(n)) } */
/** @ensures{safe} forall (n: int ∈ [0, 10)) { Number.isSafeInteger(triple(n)) } */
export function triple(x: number): number {
  return x * 3;
}
