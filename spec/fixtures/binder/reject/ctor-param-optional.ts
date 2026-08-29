// An optional constructor parameter is refused: an omitted argument
// takes the value undefined, which no generation domain contains.
export class Offset {
  public readonly x: number;
  public readonly y: number;

  constructor(x: number, y?: number) {
    this.x = x;
    this.y = y ?? 0;
  }
}

/** @ensures{selfSame} forall (o: Offset) { shift(o) === shift(o) } */
export function shift(o: Offset): number {
  return o.x + o.y;
}
