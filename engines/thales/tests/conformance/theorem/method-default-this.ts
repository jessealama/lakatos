export class Counter {
  readonly n: number;
  constructor(n: number) {
    this.n = n;
  }
  /** @ensures{p} forall (x: int ∈ [0, 4)) { Object.is(new Counter(x).twice(), x + x) } */
  twice(by: number = this.n): number {
    return this.n + by;
  }
}
