// A domain that is neither a primitive nor a class declared in this
// module resolves to nothing.
/** @ensures{reflexive} forall (x: float) { same(x) === same(x) } */
export function same(x: number): number {
  return x;
}
