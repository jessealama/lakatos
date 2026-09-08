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

export class Reading {
  readonly value: number | undefined;
  constructor(value: number) {
    this.value = value;
  }
  /** @ensures{readsBack} forall (a: number) { Object.is(new Reading(a).get(), a) } */
  get(): number {
    return this.value === undefined ? 0 : this.value;
  }
  /** @ensures{typeofNarrows} forall (a: number) { Object.is(new Reading(a).narrow(), a) } */
  narrow(): number {
    if (typeof this.value === "number") {
      return this.value;
    }
    return 0;
  }
}

export class Pair {
  readonly inner: Inner;
  constructor(i: Inner) {
    this.inner = i;
  }
  /** @ensures{delegates} forall (a: number) { Object.is(new Pair(new Inner(a)).peek(), a) } */
  peek(): number {
    return this.inner.v;
  }
}
