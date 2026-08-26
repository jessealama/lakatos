/** @ensures{guarded} forall (n: int ∈ [0, 2)) { n ≡ 1 -> pick(n) === 1 } */
export function pick(n: number): number {
  if (Object.is(n, 1)) {
    return 1;
  }
  return 0;
}
