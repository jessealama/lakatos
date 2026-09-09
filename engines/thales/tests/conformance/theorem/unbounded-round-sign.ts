/** @ensures{atMostOne} forall (x: number) { Number.isFinite(x) -> unit(x) <= 1 } */
/** @ensures{atLeastMinusOne} forall (x: number) { Number.isFinite(x) -> unit(x) >= -1 } */
export function unit(x: number): number {
  return Math.sign(x);
}
/** @ensures{atMostCeil} forall (x: number) { Number.isFinite(x) -> nearest(x) <= up(x) } */
/** @ensures{atLeastFloor} forall (x: number) { Number.isFinite(x) -> nearest(x) >= down(x) } */
export function nearest(x: number): number {
  return Math.round(x);
}
export function up(x: number): number {
  return Math.ceil(x);
}
export function down(x: number): number {
  return Math.floor(x);
}
