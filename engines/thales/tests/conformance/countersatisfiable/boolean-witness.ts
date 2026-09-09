// A false claim over a boolean binder ships the witness the enumeration
// finds first — false before true, the order the refuter walks too — so
// both engines report the same assignment.

/** @ensures{alwaysPicks} forall (n: int ∈ [0, 4)) (b: boolean) { pick(n, b) === n } */
export function pick(n: number, b: boolean): number {
  if (b) {
    return n;
  }
  return 0;
}

/** @ensures{onlyOff} forall (b: boolean) { flip(b) } */
export function flip(b: boolean): boolean {
  return !b;
}
