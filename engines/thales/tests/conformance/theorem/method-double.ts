export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{doubled} forall (x: number) { Object.is(new Box(x).double(), x * 2) } */
  double(): number {
    return this.#v * 2;
  }
}
