/** A nested class binder: the Span quantifier bottoms out in the numbers
 * two Points are built from, and a throw at either level discards. */
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

  /** @ensures{nonNegative} ∀ (s : Span) { 0 <= s.length() } */
  length(): number {
    return Math.abs(this.dx) + Math.abs(this.dy);
  }
}
