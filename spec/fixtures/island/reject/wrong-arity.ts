export function scale(x: number, factor: number): number {
  return x * factor;
}
/** @ensures{p} forall (x: int ∈ [0, 5)) { scale(x) >= 0 } */
export function id(x: number): number {
  return x;
}
