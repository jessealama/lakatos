// An unbounded binder with a guard: the residual sits in the arm the
// guard refutes, and the taken arm is the identity.
/** @ensures{keeps} forall (x: number) { 0 <= x → 0 <= nonNegative(x) } */
export function nonNegative(x: number): number {
  if (x < 0) {
    return Math.log(x);
  }
  return x;
}
