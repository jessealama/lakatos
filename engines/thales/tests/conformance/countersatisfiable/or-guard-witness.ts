// The conclusion is false at x = 0 too, so a witness that ignored the guard
// would report it; the reported one must satisfy the disjunction.
/** @ensures{picksOne} forall (x: int in [0, 4)) { x === 1 ∨ x === 3 → bit(x) === 1 } */
export function bit(x: number): number {
  if (x === 1 || x === 3) {
    return 0;
  }
  return x;
}
