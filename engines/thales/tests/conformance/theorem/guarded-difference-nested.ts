// The ordering guard one image level down: a Span of two Points guards
// `p.x <= q.x` and stores the difference, so the proof has to carry the
// Points' own finiteness guards through the Span's guard to the width.
export class Point {
  public readonly x: number;

  constructor(x: number) {
    if (x === -Infinity || x === Infinity) {
      throw new RangeError("Cannot accept an infinite coordinate");
    }
    this.x = x;
  }
}

export class Span {
  public readonly d: number;

  constructor(p: Point, q: Point) {
    if (!(p.x <= q.x)) {
      throw new RangeError("Span must run left to right");
    }
    this.d = q.x - p.x;
  }

  /**
   * @ensures{nonNegative} ∀ (s : Span) { 0 <= s.width() }
   */
  width(): number {
    return this.d;
  }
}
