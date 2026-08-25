// A `#private` member is unreachable from outside, so no caller can observe it.
export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  get #v(): number {
    return 0;
  }
}
