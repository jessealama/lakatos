// Five guards over four fields, two of them on fields the property never
// reads: those guards double the inverted image without changing what any
// leaf of it means, so the proof must not pay for them.
export class Wide {
  readonly w: number;
  readonly x: number;
  readonly y: number;
  readonly z: number;

  constructor(w: number, x: number, y: number, z: number) {
    if (!Number.isFinite(x) || !Number.isFinite(y)) {
      throw new RangeError("coordinates must be finite");
    }
    if (Object.is(w, -0)) {
      w = 0;
    }
    if (Object.is(x, -0)) {
      x = 0;
    }
    if (Object.is(y, -0)) {
      y = 0;
    }
    if (Object.is(z, -0)) {
      z = 0;
    }
    this.w = w;
    this.x = x;
    this.y = y;
    this.z = z;
  }

  /** @ensures{nonNegative} ∀ (p q : Wide) { 0 <= p.distance(q) } */
  distance(q: Wide): number {
    const dx = this.x - q.x;
    const dy = this.y - q.y;
    return Math.sqrt(dx * dx + dy * dy);
  }
}
