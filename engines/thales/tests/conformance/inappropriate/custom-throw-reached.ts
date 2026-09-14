// `Foo` is not one of the seven builtin error classes, so the throw is a
// residual site. This domain reaches the arm the site is in, so the property
// is about code outside the model. The other arm returns a constant so that
// the site is the only thing left unclosed: a leaf the model's own
// arithmetic stops is a GaveUp, not an Inappropriate.
class Foo {}

/** @ensures{positive} forall (a: int ∈ [-2, 5)) { guard(a) > 0 } */
export function guard(a: number): number {
  if (a < 0) throw new Foo();
  return 1;
}
