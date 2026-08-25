/** Boxed value — shows @ensures on a getter and on a constructor. */
export class Box {
  #v: number;

  /** @ensures{constructorKeepsIt} forall (x: int) { new Box(x).v === x } */
  constructor(v: number) {
    this.#v = v;
  }

  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */
  get v(): number {
    return this.#v;
  }
}
