/** @ensures{alwaysOne} forall (n: int ∈ [0, 2)) { flag(n) === 1 } */
export function flag(n: number): number {
  if (Object.is(n, 0)) {
    return 1;
  }
  return 0;
}
