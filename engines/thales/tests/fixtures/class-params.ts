export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{selfGap} forall (a: int ∈ [0, 10)) { Object.is(new Point(a).gap(new Point(a)), 0) } */
  gap(other: Point): number {
    return other.x - this.x;
  }
  /** @ensures{doubleGap} forall (a: int ∈ [0, 10)) { Object.is(new Point(a).twice(new Point(a)), 0) } */
  twice(other: Point): number {
    return other.gap(other) + this.gap(other);
  }
}

export class Wrap {
  readonly x: number;
  constructor(p: Point) {
    this.x = p.x;
  }
  /** @ensures{unwraps} forall (a: int ∈ [0, 10)) { Object.is(new Wrap(new Point(a)).v, a) } */
  get v(): number {
    return this.x;
  }
}

/** @ensures{reads} forall (a: int ∈ [0, 10)) { Object.is(readX(new Point(a)), a) } */
export function readX(p: Point): number {
  return p.x;
}
