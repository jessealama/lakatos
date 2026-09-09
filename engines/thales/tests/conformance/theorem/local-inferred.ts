// An unannotated local binds at its initializer's static type: a
// construction at its class, an identifier at what it is bound to — a
// parameter, an earlier local, a class-typed field read — and a union
// parameter at its union; a number-valued initializer stays a number.
export class Pt {
  readonly x: number;
  constructor(x: number) {
    this.x = x;
  }
  twice(): number {
    return this.x * 2;
  }
}

export class Box {
  readonly p: Pt;
  constructor(p: Pt) {
    this.p = p;
  }
}

/** @ensures{copies} forall (a: number) { Object.is(viaLocal(new Pt(a)), a) } */
export function viaLocal(q: Pt): number {
  const p = q;
  return p.x;
}

/** @ensures{one} forall (n: int ∈ [0, 10)) { hold(n) >= 1 } */
export function hold(n: number): number {
  const p = new Pt(1);
  return n + p.x;
}

/** @ensures{chains} forall (n: int ∈ [0, 10)) { chained(n) === 2 * n } */
export function chained(n: number): number {
  const p = new Pt(n);
  const r = p;
  return r.twice();
}

/** @ensures{unboxes} forall (n: int ∈ [0, 10)) { unboxed(new Box(new Pt(n))) === n } */
export function unboxed(b: Box): number {
  const q = b.p;
  return q.x;
}

/** @ensures{rebinds} forall (n: int ∈ [0, 10)) { rebound(n) === n + 1 } */
export function rebound(n: number): number {
  let p = new Pt(n);
  p = new Pt(p.x + 1);
  return p.x;
}

/** @ensures{numId} forall (x: number) { Object.is(carry(x), x) } */
export function carry(v: number | string): number {
  const w = v;
  if (typeof w === "number") {
    return w;
  }
  return 0;
}

/** @ensures{sums} forall (n: int ∈ [0, 10)) { summed(n) === 3 * n } */
export function summed(n: number): number {
  const p = new Pt(n);
  const m = p.x;
  const t = p.twice();
  return m + t;
}
