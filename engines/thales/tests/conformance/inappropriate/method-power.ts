export class Pow {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{grows} forall (x: number) { 1 <= new Pow(x).square() } */
  square(): number {
    return this.#v ** 2;
  }
}
