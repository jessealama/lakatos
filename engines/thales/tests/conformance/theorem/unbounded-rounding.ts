/** @ensures{noBigger} forall (x: number) { Number.isFinite(x) -> down(x) <= x } */
export function down(x: number): number {
  return Math.floor(x);
}
/** @ensures{noSmaller} forall (x: number) { Number.isFinite(x) -> up(x) >= x } */
export function up(x: number): number {
  return Math.ceil(x);
}
/** @ensures{shrinks} forall (x: number) { Number.isFinite(x) -> x >= 0 -> chop(x) <= x } */
export function chop(x: number): number {
  return Math.trunc(x);
}
/** @ensures{floorCap} forall (x: number) { Number.isFinite(x) -> floorCap(x) <= 5 } */
export function floorCap(x: number): number {
  return Math.min(Math.floor(x), 5);
}
