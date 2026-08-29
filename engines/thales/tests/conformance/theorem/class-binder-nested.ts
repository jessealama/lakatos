// A class binder whose class is built from classes: the domain expands
// through two image levels, so the proof has to carry one ctor-succeeds
// hypothesis per level and still reach the Points' own guards.
export class Point {
  public readonly x: number;
  public readonly y: number;

  constructor(x: number, y: number) {
    if (
      x === -Infinity ||
      x === Infinity ||
      y === -Infinity ||
      y === Infinity
    ) {
      throw new RangeError("Cannot accept infinite coordinates");
    }
    if (Object.is(x, NaN) || Object.is(y, NaN)) {
      throw new RangeError("Coordinates cannot be NaN");
    }
    if (Object.is(x, -0)) {
      x = 0;
    }
    if (Object.is(y, -0)) {
      y = 0;
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

  /**
   * @ensures{nonNegative} ∀ (s : Span) { 0 <= s.length() }
   */
  length(): number {
    return Math.sqrt(this.dx * this.dx + this.dy * this.dy);
  }
}
