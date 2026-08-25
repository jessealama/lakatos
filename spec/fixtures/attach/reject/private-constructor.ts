// A `private` constructor cannot be called from outside, so `new Box(x)` is
// not a thing any caller can write.
export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  private constructor(readonly n: number) {}
}
