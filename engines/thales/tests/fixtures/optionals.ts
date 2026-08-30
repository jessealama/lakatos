/**
 * @ensures{absentIsZero} forall (x: int ∈ [0, 4)) { Object.is(pick() + x, x) }
 * @ensures{presentIsArgument} forall (x: number) { Object.is(pick(x), x) }
 */
export function pick(y?: number): number {
  if (y === undefined) {
    return 0;
  }
  return y;
}

/** @ensures{defaultStep} forall (x: int ∈ [0, 4)) { Object.is(step(x), x + 1) } */
export function step(x: number, by?: number): number {
  if (by === undefined) {
    return x + 1;
  }
  return x + by;
}

export class Counter {
  readonly n: number;

  constructor(n: number) {
    this.n = n;
  }

  /** @ensures{bumpDefaults} forall (x: int ∈ [0, 4)) { Object.is(new Counter(x).bump(), x + 1) } */
  bump(by?: number): number {
    if (by === undefined) {
      return this.n + 1;
    }
    return this.n + by;
  }
}
