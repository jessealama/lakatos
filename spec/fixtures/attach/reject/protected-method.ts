// A `protected` member is unreachable from outside, so no caller can observe it.
export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  protected touch(x: number): number {
    return x;
  }
}
