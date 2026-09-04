/**
 * @ensures{omitted} forall (x: int ∈ [0, 4)) { Object.is(add(x), x) }
 * @ensures{explicit} forall (x: int ∈ [0, 4)) { Object.is(add(x, undefined), x) }
 * @ensures{supplied} forall (x: int ∈ [0, 4)) (y: int ∈ [0, 4)) { Object.is(add(x, y), x + y) }
 */
export function add(x: number, y: number = 0): number {
  return x + y;
}

/** @ensures{earlier} forall (x: int ∈ [0, 4)) { Object.is(twice(x), x * 2) } */
export function twice(x: number, y: number = x * 2): number {
  return y;
}

/** @ensures{leading} forall (x: int ∈ [0, 4)) { Object.is(lead(undefined, x), x + 1) } */
export function lead(x: number = 1, y: number): number {
  return x + y;
}

/** @ensures{mutated} forall (x: int ∈ [0, 4)) { Object.is(bump(x), x + 1) } */
export function bump(x: number, by: number = 1): number {
  by = by + 0;
  return x + by;
}

/** @ensures{nullDefault} forall (x: int ∈ [0, 4)) { Object.is(orNull(x), x) } */
export function orNull(x: number, y: number | null | undefined = null): number {
  if (y === null) {
    return x;
  }
  return y;
}

export class Counter {
  readonly n: number;

  constructor(n: number) {
    this.n = n;
  }

  /** @ensures{methodDefault} forall (x: int ∈ [0, 4)) { Object.is(new Counter(x).step(), x + 1) } */
  step(by: number = 1): number {
    return this.n + by;
  }

  /** @ensures{thisDefault} forall (x: int ∈ [0, 4)) { Object.is(new Counter(x).twice(), x + x) } */
  twice(by: number = this.n): number {
    return this.n + by;
  }
}
