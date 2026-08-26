/** @ensures{identity} forall (n: int ∈ [0, 4)) { clampInf(n) === n } */
export function clampInf(x: number): number {
  if (x === Infinity) {
    return 0;
  }
  return x;
}
