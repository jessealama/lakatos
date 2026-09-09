// A parameter and a return type may be boolean: a predicate helper is a
// boolean island over a call, a boolean parameter or binder is a
// condition, and a method or getter returning boolean is one too.

/** @ensures{small} forall (n: int ∈ [0, 3)) { isSmall(n) } */
/** @ensures{equalsTrue} forall (n: int ∈ [0, 3)) { isSmall(n) === true } */
export function isSmall(n: number): boolean {
  return n < 5;
}

/** @ensures{picks} forall (n: int ∈ [0, 10)) (b: boolean) { pick(n, b) >= 0 } */
export function pick(n: number, b: boolean): number {
  if (b) {
    return n;
  }
  return 0;
}

/** @ensures{viaHelper} forall (n: int ∈ [0, 10)) { clamp(n) >= 0 } */
export function clamp(n: number): number {
  if (isSmall(n) && n > 1) {
    return 0;
  }
  return n;
}

/** @ensures{flips} forall (b: boolean) { flip(flip(b)) === b } */
export function flip(b: boolean): boolean {
  return !b;
}

/** @ensures{defaulted} forall (n: int ∈ [0, 5)) { pickOr(n) === 0 } */
export function pickOr(n: number, b: boolean = false): number {
  if (b) {
    return n;
  }
  return 0;
}

export class Gate {
  readonly level: number;
  constructor(level: number) {
    this.level = level;
  }
  get live(): boolean {
    return this.level > 0;
  }
  isAbove(k: number): boolean {
    return this.level > k;
  }
  /** @ensures{gated} forall (n: int ∈ [0, 5)) { new Gate(n).pass(n) >= 0 } */
  pass(n: number): number {
    if (this.live && this.isAbove(n)) {
      return n;
    }
    return 0;
  }
}

/** @ensures{opens} forall (n: int ∈ [1, 5)) { new Gate(n).live } */
/** @ensures{above} forall (n: int ∈ [1, 5)) { new Gate(n).isAbove(0) } */
export function passes(n: number): number {
  if (new Gate(n).isAbove(0)) {
    return n;
  }
  return 0;
}
