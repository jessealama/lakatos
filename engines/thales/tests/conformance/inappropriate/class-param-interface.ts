export interface Named {
  x: number;
}

export class Point {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 10)) { Object.is(new Point(a).near(a), 0) } */
  near(other: Named): number {
    return this.x;
  }
}
