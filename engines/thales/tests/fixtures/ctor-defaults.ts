export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }

  /** @ensures{omitted} forall (a: int ∈ [0, 4)) { Object.is(new P(a).span(), a * a) } */
  span(): number {
    return this.x * this.x + this.y * this.y;
  }
}

/** @ensures{binder} forall (p: P) { Object.is(sum(p), p.x + p.y) } */
export function sum(p: P): number {
  return p.x + p.y;
}
