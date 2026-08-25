// A public static getter of an exported class. Qualified name: `Box.origin`.
export class Box {
  /** @ensures{originIsZero} forall (x: int) { Box.origin === 0 } */
  static get origin(): number {
    return 0;
  }
}
