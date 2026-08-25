// A default-exported class is not an admissible domain: the export has
// no fixed spelling for the identity to rest on.
export default class Point {
  public readonly x: number;

  constructor(x: number) {
    this.x = x;
  }
}

/** @ensures{selfSame} forall (p: Point) { travel(p) === travel(p) } */
export function travel(p: Point): number {
  return p.x;
}
