/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { rebound(x) >= 0 } */
export function rebound(x: number): number {
  const y = 1;
  if (x > 0) {
    const y = 2;
    return y;
  }
  return y;
}
