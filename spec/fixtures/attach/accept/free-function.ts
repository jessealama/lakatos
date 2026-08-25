// An exported function declaration. Qualified name: `bump`.
/** @ensures{bumpAddsOne} forall (x: int) { bump(x) === x + 1 } */
export function bump(x: number): number {
  return x + 1;
}
