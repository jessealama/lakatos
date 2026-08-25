// A rest constructor parameter is refused: it has no fixed arity to
// generate for.
export class Path {
  public readonly length: number;

  constructor(...xs: number[]) {
    this.length = xs.length;
  }
}

/** @ensures{selfSame} forall (p: Path) { span(p) === span(p) } */
export function span(p: Path): number {
  return p.length;
}
