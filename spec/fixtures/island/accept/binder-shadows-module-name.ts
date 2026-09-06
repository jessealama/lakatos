export const x = 3;
/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */
export function f(x: number): number {
  return x;
}
