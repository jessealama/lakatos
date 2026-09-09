/** @ensures{bounded} forall (n: int ∈ [0, 100)) { keep(n) <= Number.MAX_SAFE_INTEGER } */
export function keep(x: number): number {
  return x;
}
