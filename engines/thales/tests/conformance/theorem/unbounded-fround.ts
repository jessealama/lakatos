/** @ensures{keepsSign} forall (x: number) { x >= 0 -> narrow(x) >= 0 } */
export function narrow(x: number): number {
  return Math.fround(x);
}

/** @ensures{staysUnderCap} forall (x: number) { x <= 100 -> capped(x) <= 100 } */
export function capped(x: number): number {
  return Math.fround(x);
}
