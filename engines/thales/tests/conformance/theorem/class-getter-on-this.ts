export class Box {
  readonly v: number;
  constructor(v: number) {
    this.v = v;
  }
  get twice(): number {
    return this.v * 2;
  }
  get quad(): number {
    return this.twice * 2;
  }
  /** @ensures{viaThis} forall (a: number) { Object.is(new Box(a).direct(), a * 2) } */
  direct(): number {
    return this.twice;
  }
  /** @ensures{viaEarlierGetter} forall (a: number) { Object.is(new Box(a).chained(), a * 2 * 2) } */
  chained(): number {
    return this.quad;
  }
}

/** @ensures{viaFresh} forall (a: number) { Object.is(new Box(a).twice, a * 2) } */
export function fresh(a: number): number {
  return new Box(a).twice;
}

/** @ensures{viaVar} forall (b: Box) { Object.is(fromVar(b), b.twice) } */
export function fromVar(b: Box): number {
  return b.twice;
}
