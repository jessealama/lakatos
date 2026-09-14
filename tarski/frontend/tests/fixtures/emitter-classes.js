"use strict";
// The class fixtures `lakatos prove` proves `Theorem`s over, stripped of
// their type annotations and their `export`s, with each `@ensures`
// instantiated at one witness. Two constructor parameter defaults are
// gone with the types — defaults are #393's — so every probe below
// passes the argument the default would have supplied.
let ok = true;

// engines/thales/tests/fixtures/classes.ts
class Box {
  #v;
  constructor(v) {
    this.#v = v;
  }
  get v() {
    return this.#v;
  }
}
class Gate {
  #lo;
  constructor(a) {
    if (a < 0) {
      throw new RangeError("negative");
    } else {
      this.#lo = a;
    }
  }
  get lo() {
    return this.#lo;
  }
}
class Doubler {
  #v;
  constructor(v) {
    this.#v = v;
  }
  double() {
    return this.#v * 2;
  }
  base() {
    return this.#v;
  }
  twice() {
    return this.base() + this.base();
  }
}
ok =
  ok &&
  Object.is(new Box(2).v, 2) &&
  Object.is(new Gate(3).lo, 3) &&
  Object.is(new Doubler(4).double(), 8) &&
  Object.is(new Doubler(4).twice(), 8);

// engines/thales/tests/fixtures/class-params.ts. `Point`'s `x = 0`
// default is #393's, so every `new Point(...)` here is explicit.
class Point {
  x;
  constructor(x) {
    this.x = x;
  }
  gap(other) {
    return other.x - this.x;
  }
  twice(other) {
    return other.gap(other) + this.gap(other);
  }
}
class Wrap {
  x;
  constructor(p) {
    this.x = p.x;
  }
  get v() {
    return this.x;
  }
}
function readX(p) {
  return p.x;
}
ok =
  ok &&
  Object.is(new Point(3).gap(new Point(3)), 0) &&
  Object.is(new Point(3).twice(new Point(3)), 0) &&
  Object.is(new Wrap(new Point(5)).v, 5) &&
  Object.is(readX(new Point(7)), 7);

// engines/thales/tests/fixtures/nested-class-binder.ts. Its `Point` is a
// different class from the one above, which is why each block is its own.
{
  class Point {
    x;
    constructor(x) {
      if (x === -Infinity || x === Infinity) {
        throw new RangeError("Cannot accept an infinite coordinate");
      }
      this.x = x;
    }
  }
  class Span {
    d;
    constructor(p, q) {
      this.d = q.x - p.x;
    }
    width() {
      return this.d;
    }
  }
  ok =
    ok &&
    new Span(new Point(1), new Point(3)).width() ===
      new Span(new Point(1), new Point(3)).width();
}

// engines/thales/tests/conformance/theorem/boolean-classes.ts. `Switch`'s
// `on = false` default is #393's, so the probe passes it.
class Flag {
  on;
  constructor(on) {
    this.on = on;
  }
  level() {
    if (this.on) {
      return 1;
    }
    return 0;
  }
}
function pick(f) {
  if (f.on) {
    return 1;
  }
  return 0;
}
function read(n, f) {
  if (f.on) {
    return n;
  }
  return 0;
}
class Switch {
  on;
  constructor(n, on) {
    this.on = n > 0 || on;
  }
  level() {
    if (this.on) {
      return 1;
    }
    return 0;
  }
}
ok =
  ok &&
  new Flag(true).level() >= 0 &&
  pick(new Flag(false)) >= 0 &&
  read(3, new Flag(true)) >= 0 &&
  new Switch(1, false).level() >= 0;

ok;
