export class C {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { new C(a).plus() >= 0 } */
  plus(k: number = 1): number {
    return this.x + k;
  }
}
