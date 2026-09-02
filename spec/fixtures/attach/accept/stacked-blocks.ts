// Two JSDoc blocks stacked on one declaration: each block's tag is its own
// annotation, in source order. Qualified name: `keep`.
/** @ensures{lower} forall (x: int) { keep(x) >= x } */
/** @ensures{upper} forall (x: int) { keep(x) <= x + 1 } */
export function keep(x: number): number {
  return x + 1;
}
