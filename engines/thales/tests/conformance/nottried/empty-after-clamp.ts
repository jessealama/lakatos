/** @ensures{vacuous} forall (x: int ∈ [1000000000000000000000000000000, 10000000000000000000000000000000]) { vac(x) >= 0 } */
export function vac(x: number): number {
  return x;
}
