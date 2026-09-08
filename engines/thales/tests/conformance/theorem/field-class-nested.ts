// A class-typed field is a receiver for its own members: the outer
// method delegates to the inner instance's method through the field.
export class Inner {
  readonly v: number;

  constructor(v: number) {
    this.v = v;
  }

  double(): number {
    return this.v * 2;
  }
}

export class Outer {
  readonly inner: Inner;

  constructor(inner: Inner) {
    this.inner = inner;
  }

  /** @ensures{delegates} forall (x: number) { Object.is(new Outer(new Inner(x)).twice(), x * 2) } */
  twice(): number {
    return this.inner.double();
  }
}
