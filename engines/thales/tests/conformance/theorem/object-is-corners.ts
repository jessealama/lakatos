/** @ensures{corners} forall (n: int ∈ [0, 2)) { zeroKind(n) === 1 } */
export function zeroKind(n: number): number {
  if (Object.is(-0, 0)) {
    return 0;
  }
  if (Object.is(0 / 0, 0 / 0)) {
    return 1;
  }
  return 2;
}
