export class P {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { new P(a).span() >= 0 } */
  span(): number {
    return this.x * this.x + this.y * this.y;
  }
}
