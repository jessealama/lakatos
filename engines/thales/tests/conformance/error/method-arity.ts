export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{p} forall (x: number) { Object.is(new Box(x).double(1), x * 2) } */
  double(): number {
    return this.#v * 2;
  }
}
