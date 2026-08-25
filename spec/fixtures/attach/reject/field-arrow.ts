// A field initialized with an arrow function is a property, not a method: it is
// reassignable, so the annotation would not pin the callee.
export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  probe = (x: number): number => x;
}
