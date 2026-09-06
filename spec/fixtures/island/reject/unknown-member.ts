export class Point {
  constructor(readonly x: number) {}
}
/** @ensures{p} forall (p: Point) { p.nope >= 0 } */
export function norm(p: Point): number {
  return p.x;
}
