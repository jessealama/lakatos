// The constructor of an exported class. Qualified name: `Box#constructor`.
export class Box {
  /** @ensures{keepsItsArgument} forall (x: int) { new Box(x).n === x } */
  constructor(readonly n: number) {}
}
