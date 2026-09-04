export class Q {
  readonly x: number;
  readonly y: number;
  constructor(x: number, y: number = this.z) {
    this.x = x;
    this.y = y;
  }
  /** @ensures{p} forall (a: int ∈ [0, 5)) { new Q(a).z >= 0 } */
  get z(): number {
    return this.y;
  }
}
