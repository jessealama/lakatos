export class Math {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{own} forall (x: number) { Object.is(new Math(x).abs(), x) } */
  abs(): number {
    return this.#v;
  }
}

export class Number {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{kept} forall (x: number) { Object.is(new Number(x).value(), x) } */
  value(): number {
    return this.#v;
  }
}
