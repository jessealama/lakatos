/** @ensures{smallestArgument} forall (n: int ∈ [0, 5)) { middle(n) === n } */
export function middle(x: number): number {
  return Math.min(x + 1, x, x + 2);
}
