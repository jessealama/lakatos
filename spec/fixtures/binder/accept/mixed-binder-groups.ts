// A class binder alongside a guarded primitive binder group.
export class Meter {
  public readonly value: number;

  constructor(value: number) {
    if (Number.isNaN(value)) {
      throw new RangeError("value must not be NaN");
    }
    this.value = value;
  }

  /** @ensures{selfSame} forall (m: Meter) (k: number ∈ (-∞, ∞)) { m.scaled(k) === m.scaled(k) } */
  scaled(k: number): number {
    return this.value * k;
  }
}
