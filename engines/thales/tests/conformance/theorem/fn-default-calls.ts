export function two(): number {
  return 2;
}
export function scale(x: number, k: number = Math.sqrt(two() * two())): number {
  return x * k;
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { Object.is(g(a), a * 2) } */
export function g(a: number): number {
  return scale(a);
}
