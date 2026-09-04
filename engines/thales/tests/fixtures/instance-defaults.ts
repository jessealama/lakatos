export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}

/**
 * @ensures{omitted} forall (a: int ∈ [0, 4)) { Object.is(shift(a), a + 1) }
 * @ensures{explicit} forall (a: int ∈ [0, 4)) { Object.is(shift(a, undefined), a + 1) }
 * @ensures{supplied} forall (a: int ∈ [0, 4)) (b: int ∈ [0, 4)) { Object.is(shift(a, new Pt(b)), a + b) }
 */
export function shift(a: number, p: Pt = new Pt(1)): number {
  return a + p.x;
}

export class Seg {
  readonly a: number;
  readonly b: number;
  constructor(a: Pt, b: Pt = new Pt(0)) {
    this.a = a.x;
    this.b = b.x;
  }

  /** @ensures{ctorDefault} forall (x: int ∈ [0, 4)) { Object.is(new Seg(new Pt(x)).len(), 0 - x) } */
  len(): number {
    return this.b - this.a;
  }
}

/** @ensures{binder} forall (s: Seg) { Object.is(span(s), s.b - s.a) } */
export function span(s: Seg): number {
  return s.b - s.a;
}
