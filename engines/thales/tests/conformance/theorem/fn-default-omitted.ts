export function add(x: number, y: number = 0): number {
  return x + y;
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { add(a) >= 0 } */
export function g(a: number): number {
  return add(a);
}
