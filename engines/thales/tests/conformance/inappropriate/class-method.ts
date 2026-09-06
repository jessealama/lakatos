export class Counter {
  /** @ensures{bumps} forall (n: int ∈ [0, 10)) { new Counter().bump(n) > n } */
  bump(n: number): number {
    return n + 1;
  }
}
