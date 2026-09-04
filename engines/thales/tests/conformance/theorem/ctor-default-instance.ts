export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}

export class Seg {
  readonly a: number;
  readonly b: number;
  constructor(a: Pt, b: Pt = new Pt(0)) {
    this.a = a.x;
    this.b = b.x;
  }

  /** @ensures{p} forall (x: int ∈ [0, 4)) { Object.is(new Seg(new Pt(x)).len(), 0 - x) } */
  len(): number {
    return this.b - this.a;
  }
}
