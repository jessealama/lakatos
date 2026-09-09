// A field or a constructor parameter at boolean is still outside the
// model: only parameters, returns, binders, and locals are.

export class Flag {
  readonly on: boolean;
  constructor(n: number) {
    this.on = n > 0;
  }
  /** @ensures{p} forall (n: int ∈ [0, 3)) { new Flag(n).read() >= 0 } */
  read(): number {
    return 0;
  }
}
