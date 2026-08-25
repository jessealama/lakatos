// A member of a non-exported class is unreachable from outside the module.
class Box {
  /** @ensures{p} forall (x: int) { new Box(x).v === x } */
  get v(): number {
    return 0;
  }
}
