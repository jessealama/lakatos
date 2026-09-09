// A class-typed local: bound at its annotation from an identifier or a
// construction, read as a place for its class's fields and methods, and
// reassigned at its class when mutable.
export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  twice(): number {
    return this.x * 2;
  }
}

/** @ensures{copies} forall (p: Pt) { Object.is(viaLocal(p), p.x) } */
export function viaLocal(q: Pt): number {
  const p: Pt = q;
  return p.x;
}

/** @ensures{doubles} forall (n: int ∈ [0, 10)) { held(n) === 2 * n } */
export function held(n: number): number {
  const p: Pt = new Pt(n);
  return p.twice();
}

/** @ensures{rebinds} forall (n: int ∈ [0, 10)) { rebound(n) === n + 1 } */
export function rebound(n: number): number {
  let p: Pt = new Pt(n);
  p = new Pt(p.x + 1);
  return p.x;
}
