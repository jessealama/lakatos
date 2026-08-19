/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { fetchTotal(x) >= 0 } */
export function fetchTotal(x: number): number {
  return await remote(x);
}
