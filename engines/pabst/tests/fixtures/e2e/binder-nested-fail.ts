/** A false claim over a nested class binder: the counterexample names the
 * whole construction, both Points included. */
export class Point {
  public readonly x: number;
  public readonly y: number;

  constructor(x: number, y: number) {
    if (!Number.isFinite(x) || !Number.isFinite(y)) {
      throw new RangeError("coordinates must be finite");
    }
    this.x = x;
    this.y = y;
  }
}

export class Span {
  public readonly dx: number;
  public readonly dy: number;

  constructor(p: Point, q: Point) {
    this.dx = q.x - p.x;
    this.dy = q.y - p.y;
  }

  /** @ensures{tight} ∀ (s : Span) { s.length() < 1000 } */
  length(): number {
    return Math.abs(this.dx) + Math.abs(this.dy);
  }
}
