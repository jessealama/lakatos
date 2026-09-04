export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}
/** @ensures{p} forall (p: P) { Object.is(sum(p), p.x + p.y) } */
export function sum(p: P): number {
  return p.x + p.y;
}
