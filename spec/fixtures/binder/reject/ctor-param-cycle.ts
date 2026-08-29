// A direct constructor-parameter cycle is refused: Node's domain would
// need a Node already in hand, so there is no base case to generate from.
export class Node {
  public readonly depth: number;

  constructor(next: Node) {
    this.depth = next.depth + 1;
  }
}

/** @ensures{selfSame} forall (n: Node) { depthOf(n) === depthOf(n) } */
export function depthOf(n: Node): number {
  return n.depth;
}
