export class Gate {
  #lo: number;
  constructor(a: number) {
    if (a < 0) {
      throw new RangeError("negative");
    } else {
      this.#lo = a;
    }
  }
  /** @ensures{kept} forall (a: number) { 0 <= a → Object.is(new Gate(a).level(), a) } */
  level(): number {
    return this.#lo;
  }
}
