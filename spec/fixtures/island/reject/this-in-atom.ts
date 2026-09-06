export class Counter {
  constructor(readonly n: number) {}
  /** @ensures{p} forall (c: Counter) { this.n >= 0 } */
  twice(): number {
    return this.n * 2;
  }
}
