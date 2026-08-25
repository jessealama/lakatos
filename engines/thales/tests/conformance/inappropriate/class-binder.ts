export class Box {
  constructor(readonly size: number) {}
}

/** @ensures{scaled} forall (b: Box) { scale(1) >= 0 } */
export function scale(x: number): number {
  return x;
}
