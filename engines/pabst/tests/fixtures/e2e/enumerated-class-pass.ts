/** Two boolean slots: four constructions, all walked. */
export class Flag {
  constructor(
    public readonly on: boolean,
    public readonly armed: boolean,
  ) {}
  live(): boolean {
    return this.on && this.armed;
  }
}

/** @ensures{sound} forall (f: Flag) { live(f) === (f.on && f.armed) } */
export function live(f: Flag): boolean {
  return f.live();
}

/** No slots: exactly one construction. */
export class Unit {
  size(): number {
    return 1;
  }
}

/** @ensures{unit} forall (u: Unit) { u.size() === 1 } */
export function size(u: Unit): number {
  return u.size();
}

/** A class-typed slot contributes its own product: 4 × 4 = 16. */
export class Pair {
  constructor(
    public readonly a: Flag,
    public readonly b: Flag,
  ) {}
  both(): boolean {
    return this.a.live() && this.b.live();
  }
}

/** @ensures{nested} forall (p: Pair) { p.both() === (p.a.live() && p.b.live()) } */
export function both(p: Pair): boolean {
  return p.both();
}

/** @ensures{mixed} forall (f: Flag) (b: boolean) { gate(f, b) === (b && f.live()) } */
export function gate(f: Flag, b: boolean): boolean {
  return b && f.live();
}

/** Refuses one of its four tuples; the walk skips it and still counts it. */
export class Latch {
  constructor(
    public readonly on: boolean,
    public readonly armed: boolean,
  ) {
    if (on && !armed) throw new RangeError("an unarmed latch cannot be on");
  }
}

/** @ensures{partialThrow} forall (l: Latch) { armedIfOn(l) } */
export function armedIfOn(l: Latch): boolean {
  return !l.on || l.armed;
}

/** Refuses both tuples: a vacuous walk is still a Theorem over two cases. */
export class Never {
  constructor(public readonly on: boolean) {
    throw new RangeError("no instance");
  }
}

/** @ensures{allThrow} forall (n: Never) { impossible(n) } */
export function impossible(n: Never): boolean {
  return n.on && !n.on;
}

/** A number slot keeps the class on the sampled path. */
export class Counter {
  constructor(public readonly n: number) {}
}

/** @ensures{sampled} forall (c: Counter) { same(c) } */
export function same(c: Counter): boolean {
  return Object.is(c.n, c.n);
}
