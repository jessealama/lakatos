class Base {}

export class Tagged extends Base {
  #v: number;
  constructor(v: number) {
    super();
    this.#v = v;
  }
  /** @ensures{keeps} forall (x: number) { Object.is(new Tagged(x).v, x) } */
  get v(): number {
    return this.#v;
  }
}
