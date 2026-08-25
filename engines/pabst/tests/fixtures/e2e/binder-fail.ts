/** A false claim over class binders: distances exceed any fixed bound. */
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

  /** @ensures{tight} ∀ (p q : Point) { p.distance(q) < 1000 } */
  distance(p: Point): number {
    const dx = p.x - this.x;
    const dy = p.y - this.y;
    return Math.sqrt(dx * dx + dy * dy);
  }
}
