// An abstract member has no body, so there is nothing to check it against.
export abstract class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  abstract probe(x: number): number;
}
