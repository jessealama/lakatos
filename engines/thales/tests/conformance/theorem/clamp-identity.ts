/** @ensures{identityBelow} forall (x: number) { Number.isFinite(x) -> x <= 5 -> capAt5(x) === x } */
export function capAt5(x: number): number {
  return Math.min(x, 5);
}
/** @ensures{identityAbove} forall (x: number) { Number.isFinite(x) -> x >= 0 -> floorAt0(x) === x } */
export function floorAt0(x: number): number {
  return Math.max(0, x);
}
/** @ensures{identityOnRange} forall (x: number) { Number.isFinite(x) -> x >= 0 -> x <= 5 -> clamp(x) === x } */
export function clamp(x: number): number {
  return Math.min(Math.max(x, 0), 5);
}
