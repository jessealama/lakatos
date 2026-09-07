/** @ensures{small} forall (x: int in [0, 10)) { x === 0 ∨ x === 1 → double(x) <= 2 } */
export function double(x: number): number {
  return x + x;
}

// Theorem only because the left disjunct settles x = 0 before the right
// side runs; a lowering that evaluated both sides would refute it there.
/** @ensures{leftSettles} forall (x: int in [0, 4)) { x === 0 ∨ reciprocal(x) > 0 } */
export function reciprocal(x: number): number {
  if (x === 0) {
    throw new RangeError("cannot invert zero");
  }
  return 1 / x;
}

// The same disjunction as a guard: it holds on the whole domain, so the
// claim under it must too.
/** @ensures{guardSettles} forall (x: int in [0, 4)) { x === 0 ∨ reciprocal(x) > 0 → double(x) >= 0 } */
export function doubleAgain(x: number): number {
  return double(x);
}
