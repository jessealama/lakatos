/** @ensures{nanOut} forall (n: int ∈ [1, 3)) { Object.is(negRoot(n), NaN) } */
export function negRoot(x: number): number {
  return Math.sqrt(-x);
}
