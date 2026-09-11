// A field and a constructor parameter may be boolean: the field is a Bool
// structure field, a read of it is a condition, the constructor parameter
// heads a class binder's spine, and a construction passes a literal.

export class Flag {
  readonly on: boolean;
  constructor(on: boolean) {
    this.on = on;
  }
  /** @ensures{reads} forall (f: Flag) { f.level() >= 0 } */
  level(): number {
    if (this.on) {
      return 1;
    }
    return 0;
  }
}

/** @ensures{branches} forall (f: Flag) { pick(f) >= 0 } */
export function pick(f: Flag): number {
  if (f.on) {
    return 1;
  }
  return 0;
}

/** @ensures{literal} forall (n: int ∈ [0, 10)) { read(n, new Flag(true)) >= 0 } */
export function read(n: number, f: Flag): number {
  if (f.on) {
    return n;
  }
  return 0;
}

export class Switch {
  readonly on: boolean;
  constructor(n: number, on: boolean = false) {
    this.on = n > 0 || on;
  }
  /** @ensures{defaulted} forall (s: Switch) { s.level() >= 0 } */
  level(): number {
    if (this.on) {
      return 1;
    }
    return 0;
  }
}
