export class Step {
  readonly by: number;
  constructor(by: number) {
    this.by = by;
  }
}

export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  /** @ensures{p} forall (a: int ∈ [0, 4)) { Object.is(new Pt(a).plus(), a + 1) } */
  plus(s: Step = new Step(1)): number {
    return this.x + s.by;
  }
}
