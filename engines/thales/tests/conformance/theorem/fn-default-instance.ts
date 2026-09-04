export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
}

/** @ensures{p} forall (a: int ∈ [0, 4)) { Object.is(shift(a), a + 1) } */
export function shift(a: number, p: Pt = new Pt(1)): number {
  return a + p.x;
}
