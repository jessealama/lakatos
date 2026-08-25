// A class-typed constructor parameter is refused: v1 does not generate
// classes recursively.
export class Anchor {
  public readonly x: number;

  constructor(x: number) {
    this.x = x;
  }
}

export class Rope {
  public readonly from: Anchor;

  constructor(from: Anchor) {
    this.from = from;
  }
}

/** @ensures{selfSame} forall (r: Rope) { start(r) === start(r) } */
export function start(r: Rope): number {
  return r.from.x;
}
