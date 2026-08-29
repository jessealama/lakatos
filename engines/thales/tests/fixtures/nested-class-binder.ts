// A class binder whose class is built from classes: the Span quantifier
// expands to the numbers two Points are built from, one ctor-succeeds
// hypothesis per level.
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
    this.d = q.x - p.x;
  }

  /**
   * @ensures{selfSame} ∀ (s : Span) { s.width() ≡ s.width() }
   */
  width(): number {
    return this.d;
  }
}
