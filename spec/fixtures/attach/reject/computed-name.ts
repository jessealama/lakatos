// A computed name has no fixed spelling, so the identity triple cannot name it.
export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  [Symbol.iterator](): number {
    return 0;
  }
}
