// Fields beyond number: a union field written from a number and from the
// atoms, a class field written from a parameter and from a construction.
export class Inner {
  readonly v: number;
  constructor(v: number) {
    this.v = v;
  }
}

export class Cell {
  readonly value: number | undefined;
  readonly inner: Inner;
  readonly n: number;
  constructor(n: number, i: Inner) {
    if (n < 0) {
      this.value = undefined;
    } else {
      this.value = n;
    }
    this.inner = i;
    this.n = n;
  }
  /** @ensures{keepsN} forall (a: number) { Object.is(new Cell(a, new Inner(a)).n, a) } */
  get plain(): number {
    return this.n;
  }
}
