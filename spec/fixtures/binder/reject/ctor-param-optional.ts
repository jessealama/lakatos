// A defaulted constructor parameter is refused: v1 generation supplies
// every argument explicitly.
export class Offset {
  public readonly x: number;
  public readonly y: number;

  constructor(x: number, y: number = 0) {
    this.x = x;
    this.y = y;
  }
}

/** @ensures{selfSame} forall (o: Offset) { shift(o) === shift(o) } */
export function shift(o: Offset): number {
  return o.x + o.y;
}
