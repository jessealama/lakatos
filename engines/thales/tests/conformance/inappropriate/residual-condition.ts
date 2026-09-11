// A residual as the condition is evaluated on every path, and it may
// throw: both arms satisfying the claim is not enough.
declare function exotic(n: number): boolean;

/** @ensures{unit} forall (n: int ∈ [0, 5)) { pick(n) >= 0 } */
export function pick(n: number): number {
  if (exotic(n)) {
    return 1;
  }
  return 0;
}
