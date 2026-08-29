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

  /** @ensures{selfSame} ∀ (s : Span) { s.width() === s.width() } */
  width(): number {
    return this.dx;
  }
}
