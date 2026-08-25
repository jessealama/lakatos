/** A getter that clamps, annotated as though it round-tripped. */
export class ClampedBox {
  #v: number;

  constructor(v: number) {
    this.#v = v;
  }

  /** @ensures{roundTrip} forall (x: int) { new ClampedBox(x).v === x } */
  get v(): number {
    return this.#v < 0 ? 0 : this.#v;
  }
}
