// A public static method of an exported class. Qualified name: `Counter.of`.
export class Counter {
  constructor(readonly n: number) {}

  /** @ensures{ofRoundTrips} forall (x: int) { Counter.of(x).n === x } */
  static of(x: number): Counter {
    return new Counter(x);
  }
}
