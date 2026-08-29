// The design doc's original Point: finiteness spelled as refuted equality
// tests (`=== ±Infinity`, `Object.is(_, NaN)`) rather than
// `Number.isFinite`, so inverting the guards travels the beq/sameValue
// bridges instead of the isFinite pair.
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

  /**
   * @ensures{nonNegative} ∀ (p q : Point) { 0 <= p.distance(q) }
   */
  distance(p: Point): number {
    const dx = p.x - this.x;
    const dy = p.y - this.y;
    return Math.sqrt(dx * dx + dy * dy);
  }
}
