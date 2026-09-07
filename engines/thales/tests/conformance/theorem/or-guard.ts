/** @ensures{small} forall (x: int in [0, 10)) { x === 0 ∨ x === 1 → double(x) <= 2 } */
export function double(x: number): number {
  return x + x;
}

export function reciprocal(x: number): number {
  if (x === 0) {
    throw new RangeError("cannot invert zero");
  }
  return 1 / x;
}

// At x = 0 the left disjunct is true, so the throwing right side never runs;
// everywhere else the right side settles it. The guard holds on the whole
// domain and the claim must too.
/** @ensures{leftSettles} forall (x: int in [0, 4)) { x === 0 ∨ reciprocal(x) > 0 → double(x) >= 0 } */
export function doubleAgain(x: number): number {
  return double(x);
}
