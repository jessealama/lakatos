// A public instance method of an exported class. Qualified name: `Counter#inc`.
export class Counter {
  constructor(readonly n: number) {}

  /** @ensures{incAddsOne} forall (x: int) { new Counter(x).inc().n === x + 1 } */
  inc(): Counter {
    return new Counter(this.n + 1);
  }
}
