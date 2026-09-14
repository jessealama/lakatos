// `Foo` is not one of the seven builtin error classes, so the throw is a
// residual site rather than a thrown kind. The site sits in the arm this
// domain never takes, so the property is proved without reaching it.
class Foo {}

/** @ensures{positive} forall (a: int ∈ [1, 5)) { guard(a) > 0 } */
export function guard(a: number): number {
  if (a < 0) throw new Foo();
  return a;
}
