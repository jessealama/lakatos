export class Point {
  constructor(readonly x: number) {}
  get norm(): number {
    return Math.abs(this.x);
  }
}
/** @ensures{p} forall (p: Point) { p.norm >= 0 } */
export function norm(p: Point): number {
  return p.norm;
}
