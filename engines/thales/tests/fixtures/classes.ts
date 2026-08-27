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

export class Gate {
  #lo: number;
  constructor(a: number) {
    if (a < 0) {
      throw new RangeError("negative");
    } else {
      this.#lo = a;
    }
  }
  /** @ensures{keepsValue} forall (a: number) { 0 <= a → Object.is(new Gate(a).lo, a) } */
  get lo(): number {
    return this.#lo;
  }
}

export class Doubler {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{doubled} forall (x: number) { Object.is(new Doubler(x).double(), 2 * x) } */
  double(): number {
    return this.#v * 2;
  }
  base(): number {
    return this.#v;
  }
  /** @ensures{chained} forall (x: number) { Object.is(new Doubler(x).twice(), x + x) } */
  twice(): number {
    return this.base() + this.base();
  }
}
