// A union-typed place carrying `boolean` is a condition: it lowers as the
// throwing projection, the twin of the one a number position takes, and
// the narrowed path discharges it.

export class Maybe {
  readonly on: boolean | undefined;
  constructor(n: number) {
    if (n < 0) {
      this.on = undefined;
    } else {
      this.on = n > 0;
    }
  }
  /** @ensures{narrowed} forall (n: int ∈ [0, 3)) { new Maybe(n).level() >= 0 } */
  level(): number {
    if (typeof this.on === "boolean" && this.on) {
      return 1;
    }
    return 0;
  }
  /** @ensures{bare} forall (n: int ∈ [0, 3)) { new Maybe(n).plain() >= 0 } */
  plain(): number {
    if (this.on) {
      return 1;
    }
    return 0;
  }
}

/** @ensures{local} forall (n: int ∈ [0, 3)) { held(n) >= 0 } */
export function held(n: number): number {
  const w: boolean | undefined = n > 0;
  if (w) {
    return 1;
  }
  return 0;
}
