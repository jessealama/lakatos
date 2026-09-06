function g(x: number): number {
  return x;
}
/** @ensures{p} forall (x: int ∈ [0, 5)) { g(x) >= 0 } */
export function f(x: number): number {
  return x;
}
