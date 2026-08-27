export class Clamp {
  #v!: number;
  constructor(v: number) {
    if (v < 0) {
      this.#v = 0;
    }
  }
  /** @ensures{floored} forall (x: number) { 0 <= new Clamp(x).v } */
  get v(): number {
    return this.#v;
  }
}
