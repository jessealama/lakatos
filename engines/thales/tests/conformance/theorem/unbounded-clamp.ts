/** @ensures{atMost} forall (x: number) { Number.isFinite(x) -> clamp(x) <= 5 } */
/** @ensures{atLeast} forall (x: number) { Number.isFinite(x) -> clamp(x) >= 0 } */
export function clamp(x: number): number {
  return Math.min(Math.max(x, 0), 5);
}
/** @ensures{noBigger} forall (x: number) { Number.isFinite(x) -> capAt1(x) <= x } */
export function capAt1(x: number): number {
  return Math.min(x, 1);
}
