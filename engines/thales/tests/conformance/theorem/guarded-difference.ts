// An ordering guard feeding a difference: `a <= b` in the constructor,
// `0 <= b - a` in the property. The infinity guards leave NaN open; it is
// the ordering guard that rules it out, and subtraction of finite doubles
// is monotone, so the width is +0 or positive (overflow to +Infinity
// included).
export class Span {
  public readonly d: number;

  constructor(a: number, b: number) {
    if (a === -Infinity || a === Infinity) {
      throw new RangeError("finite only");
    }
    if (b === -Infinity || b === Infinity) {
      throw new RangeError("finite only");
    }
    if (!(a <= b)) {
      throw new RangeError("Span must run left to right");
    }
    this.d = b - a;
  }

  /**
   * @ensures{nonNegative} ∀ (s : Span) { 0 <= s.width() }
   */
  width(): number {
    return this.d;
  }
}
