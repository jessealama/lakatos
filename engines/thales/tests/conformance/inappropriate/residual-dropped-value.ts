// The call's value is dropped, its effect is not: an unmodeled statement
// on the taken path may throw.
declare function log(n: number): void;

/** @ensures{kept} forall (n: int ∈ [0, 5)) { traced(n) === n } */
export function traced(n: number): number {
  log(n);
  return n;
}
