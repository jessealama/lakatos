"use strict";
class Box {
  #v;
  constructor(v) {
    if (v < 0) throw new RangeError("neg");
    this.#v = v;
  }
  get v() {
    return this.#v;
  }
  scale(k) {
    return new Box(this.#v * k);
  }
}
const b = new Box(2).scale(3);
b.v === 6 && b instanceof Box;
