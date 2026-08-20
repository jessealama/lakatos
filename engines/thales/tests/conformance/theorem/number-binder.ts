/** @ensures{identity} forall (a: number ∈ (0, 1]) { echo(a) ≡ a } */
export function echo(a: number): number {
  return a;
}
