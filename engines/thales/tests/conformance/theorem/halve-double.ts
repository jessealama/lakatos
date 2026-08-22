/** @ensures{halving} forall (x: int ∈ [0, 20000)) { halve(x + x) === x } */
export function halve(x: number): number {
  return x / 2;
}
