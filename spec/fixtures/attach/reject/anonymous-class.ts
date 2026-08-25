// An anonymous class has no name, so the identity triple cannot name its class.
export default class {
  /** @ensures{p} forall (x: int) { x === x } */
  probe(x: number): number {
    return x;
  }
}
