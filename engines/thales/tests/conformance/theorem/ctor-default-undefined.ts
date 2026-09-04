export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}
/** @ensures{p} forall (a: int ∈ [0, 5)) { g(a) >= 0 } */
export function g(a: number): number {
  return new P(a, undefined).x;
}
