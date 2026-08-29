// A class-typed constructor parameter is admissible: the domain expands
// recursively, and the Anchor/Rope graph is acyclic, so it bottoms out.
export class Anchor {
  public readonly x: number;

  constructor(x: number) {
    this.x = x;
  }
}

export class Rope {
  public readonly at: number;

  constructor(from: Anchor) {
    this.at = from.x;
  }
}

/** @ensures{selfSame} forall (r: Rope) { start(r) === start(r) } */
export function start(r: Rope): number {
  return r.at;
}
