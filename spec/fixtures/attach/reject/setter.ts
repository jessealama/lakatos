// A setter has no value to speak of, so nothing can be ensured about it.
export class Box {
  #v = 0;

  /** @ensures{p} forall (x: int) { x === x } */
  set v(n: number) {
    this.#v = n;
  }
}
