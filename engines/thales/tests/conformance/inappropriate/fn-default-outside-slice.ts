export function pow(x: number, y: number = 2 ** 3): number {
  return x + y;
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */
export function g(a: number): number {
  return pow(a, 1);
}
