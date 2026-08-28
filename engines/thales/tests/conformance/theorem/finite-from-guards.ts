// A finiteness conclusion recovered purely from constructor guards: the
// binder carries no range, so isFinite must come back from the refuted
// equality tests via the strict bounds.
export class Guarded {
  readonly x: number;

  constructor(x: number) {
    if (x === -Infinity || x === Infinity) {
      throw new RangeError("infinite");
    }
    if (Object.is(x, NaN)) {
      throw new RangeError("nan");
    }
    this.x = x;
  }

  /** @ensures{finite} ∀ (p : Guarded) { Number.isFinite(p.value()) } */
  value(): number {
    return this.x;
  }
}
