// A class binder on a free function's annotation: the binder's class and
// the attachment point are independent.
export class Box {
  public readonly size: number;

  constructor(size: number) {
    if (size < 0) {
      throw new RangeError("size must be non-negative");
    }
    this.size = size;
  }
}

/** @ensures{selfSame} forall (b: Box) { volume(b) === volume(b) } */
export function volume(b: Box): number {
  return b.size * b.size * b.size;
}
