export class Acc {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  base(): number {
    return this.#v;
  }
  /** @ensures{chained} forall (x: number) { Object.is(new Acc(x).twice(), x + x) } */
  twice(): number {
    return this.base() + this.base();
  }
}
