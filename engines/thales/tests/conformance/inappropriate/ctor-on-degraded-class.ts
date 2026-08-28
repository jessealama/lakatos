export class Counter {
  readonly n: number;
  /** @ensures{nonNegative} forall (a: int ∈ [0, 10)) { 0 <= a } */
  constructor(n: string) {
    this.n = 1;
  }
}
