/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { arity(n) >= 0 } */
export function arity(x: number): number {
  return x * Number.length;
}
