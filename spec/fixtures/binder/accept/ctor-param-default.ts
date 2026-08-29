// A defaulted constructor parameter is admitted: quantification is at
// full arity, and the default inhabits its own parameter's declared
// type, so every defaulted call's instance is already in the image.
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
