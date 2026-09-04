export function lead(x: number = 1, y: number): number {
  return x + y;
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { Object.is(g(a), a + 1) } */
export function g(a: number): number {
  return lead(undefined, a);
}
