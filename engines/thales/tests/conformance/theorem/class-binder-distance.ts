// A class-valued binder over the image of a guarding constructor: the
// binder's only finiteness is what the passed guards leave behind, and the
// `-0` normalization is inside the domain by construction.
export class Point {
  readonly x: number;
  readonly y: number;

  constructor(x: number, y: number) {
    if (!Number.isFinite(x) || !Number.isFinite(y)) {
      throw new RangeError("coordinates must be finite");
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

  /** @ensures{nonNegative} ∀ (p q : Point) { 0 <= p.distance(q) } */
  distance(q: Point): number {
    const dx = this.x - q.x;
    const dy = this.y - q.y;
    return Math.sqrt(dx * dx + dy * dy);
  }
}
