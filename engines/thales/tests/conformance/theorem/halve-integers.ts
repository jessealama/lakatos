/** @ensures{nonNegative} forall (n: int ∈ [0, 1000)) { halvePosInteger(n) >= 0 } */
export function halvePosInteger(n: number): number {
  return Math.floor(n / 2);
}

/** @ensures{nonPositive} forall (n: int ∈ [-1000, 1)) { halveNegInteger(n) <= 0 } */
export function halveNegInteger(n: number): number {
  return Math.ceil(n / 2);
}
