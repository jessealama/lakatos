export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */
  get v(): number {
    return this.#v;
  }
}
