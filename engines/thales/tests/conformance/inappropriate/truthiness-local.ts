// Truthiness has no model: a number local is not a condition, even
// though a boolean local now is.

/** @ensures{p} forall (n: int ∈ [0, 10)) { f(n) >= 0 } */
export function f(n: number): number {
  const x = n + 1;
  if (x) {
    return 0;
  }
  return n;
}
