export class Pair {
  #a: number;
  constructor(a: number) {
    this.#a = a;
    this.#a = a + 1;
  }
  /** @ensures{stored} forall (x: number) { Object.is(new Pair(x).a, x) } */
  get a(): number {
    return this.#a;
  }
}
