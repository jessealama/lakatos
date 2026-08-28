export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{selfGap} forall (a: int ∈ [0, 10)) { Object.is(new Point(a).gap(new Point(a)), 0) } */
  gap(other: Point): number {
    return other.x - this.x;
  }
}
