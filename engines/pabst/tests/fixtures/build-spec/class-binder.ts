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

  /** @ensures{nonNegative} ∀ (p q : Point) { 0 <= p.distance(q) } */
  distance(p: Point): number {
    const dx = p.x - this.x;
    const dy = p.y - this.y;
    return Math.sqrt(dx * dx + dy * dy);
  }
}
