const root2 = Math.sqrt(2);
const noLimit = Infinity;

/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { diagonal(n) >= 0 } */
export function diagonal(x: number): number {
  return x * root2;
}

/** @ensures{nonNegative} forall (n: int ∈ [0, 10)) { shrink(n) >= 0 } */
export function shrink(x: number): number {
  return x / noLimit;
}
