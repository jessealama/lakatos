export class Pair {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  power(k: number): number {
    return this.#v ** k;
  }
  /** @ensures{kept} forall (x: number) { Object.is(new Pair(x).value(), x) } */
  value(): number {
    return this.#v;
  }
}
