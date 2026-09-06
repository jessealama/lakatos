/** @ensures{p} forall (x: int ∈ [0, 5)) { Math.abs(f(x)) >= 0 ∧ Number.isFinite(f(x)) } */
export function f(x: number): number {
  return x;
}
