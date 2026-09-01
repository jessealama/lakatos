import { describe, it, expect } from "vitest";
import { extractFromSource } from "../src/extract.js";
import { qualifiedName } from "../src/qualified-name.js";

const FOO = `/** @ensures{nonzero} forall (x: int) (y: number) {
 *    Number.isInteger(y) ==> foo(x, y) !== 0 } */
export function foo(x: bigint, y: number): number {
  return Number(x) + (y === 0 ? 1 : y);
}

export function helper(n: number): number {
  return n;
}
`;

describe("extract", () => {
  it("reads exported names", () => {
    const r = extractFromSource(FOO, "foo.ts");
    expect([...r.exports].sort()).toEqual(["foo", "helper"]);
  });

  it("reads the @ensures annotation attached to its function", () => {
    const r = extractFromSource(FOO, "foo.ts");
    expect(r.annotations).toHaveLength(1);
    const a = r.annotations[0]!;
    expect(a.propertyName).toBe("nonzero");
    expect(a.functionName).toBe("foo");
    expect(a.formula).toContain("forall (x: int) (y: number)");
    expect(a.formula).toContain("foo(x, y) !== 0");
    expect(a.line).toBeGreaterThan(0);
  });

  it("records every @ensures in a single JSDoc block as its own property", () => {
    const src = `/**
 * @param x the input
 * @ensures{lo} forall (x: int) { foo(x) >= 0 }
 * @ensures{hi} forall (x: int) { foo(x) <= 100 }
 */
export function foo(x: number): number { return x; }
`;
    const r = extractFromSource(src, "multi.ts");
    expect(r.annotations.map((a) => a.propertyName)).toEqual(["lo", "hi"]);
    expect(r.annotations[0]!.formula).toBe("forall (x: int) { foo(x) >= 0 }");
    expect(r.annotations[1]!.formula).toBe("forall (x: int) { foo(x) <= 100 }");
  });

  it("passes a braced body through JSDoc extraction verbatim", () => {
    const src = `/** @ensures{p} forall (x: int) { \`\${x}\` === String(x) } */
export function f(x: number): number { return x; }
`;
    const r = extractFromSource(src, "braces.ts");
    expect(r.annotations).toHaveLength(1);
    expect(r.annotations[0]!.formula).toBe(
      "forall (x: int) { `${x}` === String(x) }",
    );
  });
});

const CLASS_OK = `export class Counter {
  constructor(private readonly n: number) {}

  /** @ensures{incAddsOne} forall (x: int) { new Counter(x).inc().value === x + 1 } */
  inc(): Counter {
    return new Counter(this.n + 1);
  }

  /** @ensures{ofRoundTrips} forall (x: int) { Counter.of(x).value === x } */
  static of(x: number): Counter {
    return new Counter(x);
  }

  // no @ensures — must be left alone
  get value(): number {
    return this.n;
  }

  // no @ensures — must be left alone
  private secret(): number {
    return this.n;
  }
}

/** @ensures{incAddsOne} forall (x: int) { bump(x) === x + 1 } */
export function bump(x: number): number {
  return x + 1;
}
`;

const CLASS_PRIVATE = `export class Box {
  /** @ensures{p} forall (x: int) { Box.touch(x) === x } */
  private touch(x: number): number {
    return x;
  }
}
`;

const CLASS_ACCESSOR = `export class Box {
  constructor(private readonly n: number) {}

  /** @ensures{p} forall (x: int) { new Box(x).value === x } */
  get value(): number {
    return this.n;
  }
}
`;

const CLASS_UNEXPORTED = `class Box {
  /** @ensures{p} forall (x: int) { Box.id(x) === x } */
  static id(x: number): number {
    return x;
  }
}
`;

const CLASS_DUP = `export class Box {
  /**
   * @ensures{p} forall (x: int) { Box.id(x) === x }
   * @ensures{p} forall (x: int) { Box.id(x) === x }
   */
  static id(x: number): number {
    return x;
  }
}
`;

describe("extract — class methods", () => {
  it("records instance and static method annotations with className/isStatic", () => {
    const r = extractFromSource(CLASS_OK, "class-ok.ts");
    const inc = r.annotations.find((a) => a.functionName === "inc")!;
    expect(inc.className).toBe("Counter");
    expect(inc.isStatic).toBe(false);
    expect(inc.propertyName).toBe("incAddsOne");

    const of = r.annotations.find((a) => a.functionName === "of")!;
    expect(of.className).toBe("Counter");
    expect(of.isStatic).toBe(true);
  });

  it("leaves a free function annotation unqualified", () => {
    const r = extractFromSource(CLASS_OK, "class-ok.ts");
    const bump = r.annotations.find((a) => a.functionName === "bump")!;
    expect(bump.className).toBeUndefined();
    expect(bump.isStatic).toBeUndefined();
  });

  it("does not collide a method and a free function sharing a property name", () => {
    const r = extractFromSource(CLASS_OK, "class-ok.ts");
    // "incAddsOne" appears on both Counter#inc and bump — both are kept
    const both = r.annotations.filter((a) => a.propertyName === "incAddsOne");
    expect(both).toHaveLength(2);
  });

  it("ignores class members without @ensures", () => {
    const r = extractFromSource(CLASS_OK, "class-ok.ts");
    expect(r.annotations.some((a) => a.functionName === "value")).toBe(false);
    expect(r.annotations.some((a) => a.functionName === "secret")).toBe(false);
  });

  it("collects @ensures on a non-public method as invalid, with identity", () => {
    const r = extractFromSource(CLASS_PRIVATE, "class-private.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    const i = r.invalid[0]!;
    expect(i.propertyName).toBe("p");
    expect(i.functionName).toBe("touch");
    expect(i.className).toBe("Box");
    expect(i.isStatic).toBe(false);
    expect(i.line).toBeGreaterThan(0);
    expect(i.message).toMatch(/non-public member 'touch'/);
  });

  it("records an accessor annotation alongside its constructor", () => {
    const r = extractFromSource(CLASS_ACCESSOR, "class-accessor.ts");
    expect(r.invalid).toEqual([]);
    expect(r.annotations).toHaveLength(1);
    expect(r.annotations[0]!.functionName).toBe("value");
  });

  it("collects @ensures on a method of a non-exported class as invalid", () => {
    const r = extractFromSource(CLASS_UNEXPORTED, "class-unexported.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    const i = r.invalid[0]!;
    expect(i.functionName).toBe("id");
    expect(i.className).toBe("Box");
    expect(i.isStatic).toBe(true);
    expect(i.message).toMatch(/which is not exported/);
  });

  it("collapses all claimants of a duplicate property name into one invalid entry", () => {
    const r = extractFromSource(CLASS_DUP, "class-dup.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    const i = r.invalid[0]!;
    expect(i.propertyName).toBe("p");
    expect(i.message).toMatch(
      /duplicate property name 'p' on member 'Box\.id'/,
    );
  });

  it("keeps extracting after an invalid annotation", () => {
    const src = `class Hidden {
  /** @ensures{p} forall (x: int) { Hidden.id(x) === x } */
  static id(x: number): number { return x; }
}

/** @ensures{q} forall (x: int) { later(x) === x } */
export function later(x: number): number { return x; }
`;
    const r = extractFromSource(src, "mixed.ts");
    expect(r.annotations.map((a) => a.propertyName)).toEqual(["q"]);
    expect(r.invalid.map((i) => i.propertyName)).toEqual(["p"]);
  });

  it("a duplicate on one function leaves its distinct siblings valid", () => {
    const src = `/**
 * @ensures{dup} forall (x: int) { f(x) === x }
 * @ensures{dup} forall (x: int) { f(x) === x }
 * @ensures{ok} forall (x: int) { f(x) >= x }
 */
export function f(x: number): number { return x; }
`;
    const r = extractFromSource(src, "dup.ts");
    expect(r.annotations.map((a) => a.propertyName)).toEqual(["ok"]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.propertyName).toBe("dup");
    expect(r.invalid[0]!.message).toMatch(/duplicate property name 'dup'/);
  });

  it("attributes no verdict when a valid annotation collides with an invalid one's identity", () => {
    const src = `export class Box {
  /** @ensures{p} forall (x: int) { new Box().id(x) === x } */
  id(x: number): number { return x; }

  /** @ensures{p} forall (x: int) { x === x } */
  "id"(x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "collide.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.message).toMatch(/duplicate property name 'p'/);
  });

  it("keeps identity keys unique: duplicates on a non-exported class collapse too", () => {
    const src = `class Box {
  /**
   * @ensures{p} forall (x: int) { x === x }
   * @ensures{p} forall (x: int) { x === x }
   */
  static id(x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "dup-unexported.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
  });

  it("reports no invalid annotations for a clean file", () => {
    expect(extractFromSource(CLASS_OK, "class-ok.ts").invalid).toEqual([]);
  });

  it("collects @ensures on protected and abstract methods as invalid", () => {
    const src = `export abstract class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  protected touch(x: number): number { return x; }

  /** @ensures{q} forall (x: int) { x === x } */
  abstract probe(x: number): number;
}
`;
    const r = extractFromSource(src, "modifiers.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid.map((i) => i.propertyName).sort()).toEqual(["p", "q"]);
    expect(r.invalid[0]!.message).toMatch(/non-public member 'touch'/);
    expect(r.invalid[1]!.message).toMatch(/unsupported member 'probe'/);
  });

  it("collects an @ensures tag with a missing or malformed {name} prefix as invalid", () => {
    const src = `/**
 * @ensures forall (x: int) { f(x) === x }
 * @ensures{9bad} forall (x: int) { f(x) === x }
 * @ensures
 */
export function f(x: number): number { return x; }
`;
    const r = extractFromSource(src, "unnamed.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(3);
    for (const i of r.invalid) {
      expect(i.propertyName).toBe("<unnamed>");
      expect(i.functionName).toBe("f");
      expect(i.line).toBeGreaterThan(0);
      expect(i.message).toMatch(/missing or malformed \{name\} prefix/);
    }
  });

  it("collects a nameless @ensures on a class method as invalid", () => {
    const src = `export class Box {
  /** @ensures forall (x: int) { new Box().id(x) === x } */
  id(x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "unnamed-method.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    const i = r.invalid[0]!;
    expect(i.propertyName).toBe("<unnamed>");
    expect(i.functionName).toBe("id");
    expect(i.className).toBe("Box");
    expect(i.message).toMatch(/missing or malformed \{name\} prefix/);
  });

  it("collects a nameless @ensures on an anonymous-class method as invalid", () => {
    const src = `export default class {
  /** @ensures forall (x: int) { x === x } */
  m(x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "unnamed-anon.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    const i = r.invalid[0]!;
    expect(i.propertyName).toBe("<unnamed>");
    expect(i.functionName).toBe("m");
    expect(i.className).toBe("<anonymous>");
    expect(i.message).toMatch(/member 'm' of an anonymous class/);
  });

  it("collects a private-identifier member as invalid under its literal label", () => {
    const src = `export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  #hidden(x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "hash.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.functionName).toBe("#hidden");
    expect(r.invalid[0]!.message).toMatch(/non-public member '#hidden'/);
  });

  it("collects @ensures on a method of an anonymous class under a placeholder", () => {
    const src = `export default class {
  /** @ensures{p} forall (x: int) { x === x } */
  m(x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "anon.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    const i = r.invalid[0]!;
    expect(i.functionName).toBe("m");
    expect(i.className).toBe("<anonymous>");
    expect(i.message).toMatch(/anonymous class/);
  });

  it("keeps distinct invalid entries whose subjects share a placeholder label", () => {
    const src = `export class A {
  /** @ensures{p} forall (x: int) { x === x } */
  [Symbol.iterator](x: number): number { return x; }

  /** @ensures{p} forall (x: int) { x === x } */
  ["other"](x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "computed-two.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(2);
    expect(r.invalid.map((i) => i.functionName)).toEqual([
      "<computed>",
      "<computed>",
    ]);
  });

  it("collects a computed-name member as invalid under '<computed>'", () => {
    const src = `export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  [Symbol.iterator](): number { return 0; }
}
`;
    const r = extractFromSource(src, "computed.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.functionName).toBe("<computed>");
    expect(r.invalid[0]!.className).toBe("Box");
    expect(r.invalid[0]!.message).toMatch(/unsupported member '<computed>'/);
  });
});

const ARROW_EXPORT = `/** @ensures{idArrow} forall (x: int) { foo(x) === x } */
export const foo = (x: number): number => x;

/** @ensures{idFn} forall (x: int) { bar(x) === x } */
export const bar = function (x: number): number { return x; };
`;

const REEXPORT = `function foo(x: number): number { return x; }
function bar(x: number): number { return x; }
export { foo, bar };
`;

describe("extract — variable and re-export forms", () => {
  it("reads @ensures on arrow- and function-expression consts", () => {
    const r = extractFromSource(ARROW_EXPORT, "arrow.ts");
    expect(r.annotations.map((a) => a.functionName).sort()).toEqual([
      "bar",
      "foo",
    ]);
    expect([...r.exports].sort()).toEqual(["bar", "foo"]);
  });

  it("collects names from an `export { ... }` declaration", () => {
    const r = extractFromSource(REEXPORT, "reexport.ts");
    expect([...r.exports].sort()).toEqual(["bar", "foo"]);
  });
});

const CLASS_GETTER = `export class Box {
  #v: number;

  constructor(v: number) {
    this.#v = v;
  }

  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */
  get v(): number {
    return this.#v;
  }
}
`;

describe("extract — getter accessors", () => {
  it("records a getter annotation as an instance member", () => {
    const r = extractFromSource(CLASS_GETTER, "klass.ts");
    expect(r.invalid).toEqual([]);
    expect(r.annotations).toHaveLength(1);
    const a = r.annotations[0]!;
    expect(a.propertyName).toBe("roundTrip");
    expect(a.functionName).toBe("v");
    expect(a.className).toBe("Box");
    expect(a.isStatic).toBe(false);
    expect(qualifiedName(a.functionName, a.className, a.isStatic)).toBe(
      "Box#v",
    );
  });

  it("records a static getter annotation as a static member", () => {
    const src = `export class Box {
  /** @ensures{zero} forall (x: int) { Box.origin === 0 } */
  static get origin(): number { return 0; }
}
`;
    const r = extractFromSource(src, "static-getter.ts");
    expect(r.invalid).toEqual([]);
    expect(r.annotations).toHaveLength(1);
    const a = r.annotations[0]!;
    expect(a.functionName).toBe("origin");
    expect(a.isStatic).toBe(true);
    expect(qualifiedName(a.functionName, a.className, a.isStatic)).toBe(
      "Box.origin",
    );
  });

  it("collects @ensures on a setter as invalid", () => {
    const src = `export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  set v(n: number) { void n; }
}
`;
    const r = extractFromSource(src, "setter.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.functionName).toBe("v");
    expect(r.invalid[0]!.message).toMatch(/unsupported member 'v'/);
  });

  it("collects @ensures on an abstract getter as invalid", () => {
    const src = `export abstract class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  abstract get v(): number;
}
`;
    const r = extractFromSource(src, "abstract-getter.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.message).toMatch(/unsupported member 'v'/);
  });

  it("collects @ensures on a non-public getter as invalid", () => {
    const src = `export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  private get v(): number { return 0; }

  /** @ensures{q} forall (x: int) { x === x } */
  get #w(): number { return 0; }
}
`;
    const r = extractFromSource(src, "private-getter.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid.map((i) => i.propertyName).sort()).toEqual(["p", "q"]);
    for (const i of r.invalid) expect(i.message).toMatch(/non-public member/);
  });

  it("collects @ensures on a getter of a non-exported class as invalid", () => {
    const src = `class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  get v(): number { return 0; }
}
`;
    const r = extractFromSource(src, "unexported-getter.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.message).toMatch(/which is not exported/);
  });
});

describe("extract — constructors", () => {
  it("records a constructor annotation under the label 'constructor'", () => {
    const src = `export class Box {
  /** @ensures{accepts} forall (x: int) { new Box(x).n === x } */
  constructor(readonly n: number) {}
}
`;
    const r = extractFromSource(src, "ctor.ts");
    expect(r.invalid).toEqual([]);
    expect(r.annotations).toHaveLength(1);
    const a = r.annotations[0]!;
    expect(a.propertyName).toBe("accepts");
    expect(a.functionName).toBe("constructor");
    expect(a.className).toBe("Box");
    expect(a.isStatic).toBe(false);
    expect(qualifiedName(a.functionName, a.className, a.isStatic)).toBe(
      "Box#constructor",
    );
  });

  it("collects @ensures on a constructor of a non-exported class as invalid", () => {
    const src = `class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  constructor(readonly n: number) {}
}
`;
    const r = extractFromSource(src, "unexported-ctor.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.functionName).toBe("constructor");
    expect(r.invalid[0]!.message).toMatch(/which is not exported/);
  });

  it("does not collide a constructor and a getter sharing a property name", () => {
    const src = `export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  constructor(readonly n: number) {}

  /** @ensures{p} forall (x: int) { x === x } */
  get v(): number { return 0; }
}
`;
    const r = extractFromSource(src, "ctor-getter.ts");
    expect(r.invalid).toEqual([]);
    expect(r.annotations.map((a) => a.functionName).sort()).toEqual([
      "constructor",
      "v",
    ]);
  });
});

describe("extract — stacked JSDoc blocks", () => {
  it("reads an @ensures from every block stacked above a function, in source order", () => {
    const src = `/** @ensures{tooBig} forall (n: int ∈ [0, 10)) { keep(n) >= 5 } */
/** @ensures{atLeastOne} forall (n: int ∈ [0, 10)) { keep(n) >= 1 } */
export function keep(n: number): number {
  return n + 1;
}
`;
    const r = extractFromSource(src, "stacked.ts");
    expect(r.invalid).toEqual([]);
    expect(r.annotations.map((a) => [a.propertyName, a.line])).toEqual([
      ["tooBig", 1],
      ["atLeastOne", 2],
    ]);
    expect(r.annotations[0]!.formula).toBe(
      "forall (n: int ∈ [0, 10)) { keep(n) >= 5 }",
    );
  });

  it("reads stacked blocks above a class member", () => {
    const src = `export class Box {
  /** @ensures{lo} forall (x: int) { new Box().id(x) >= x } */
  /** @ensures{hi} forall (x: int) { new Box().id(x) <= x } */
  id(x: number): number { return x; }
}
`;
    const r = extractFromSource(src, "stacked-class.ts");
    expect(r.invalid).toEqual([]);
    expect(
      r.annotations.map((a) => [a.propertyName, a.functionName, a.className]),
    ).toEqual([
      ["lo", "id", "Box"],
      ["hi", "id", "Box"],
    ]);
  });

  it("reports a nameless @ensures in an earlier block instead of dropping it", () => {
    const src = `/** @ensures forall (x: int) { f(x) === x } */
/** @ensures{named} forall (x: int) { f(x) === x } */
export function f(x: number): number { return x; }
`;
    const r = extractFromSource(src, "stacked-unnamed.ts");
    expect(r.annotations.map((a) => a.propertyName)).toEqual(["named"]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]).toMatchObject({
      propertyName: "<unnamed>",
      functionName: "f",
      line: 1,
    });
  });

  it("collapses a property name repeated across blocks into one duplicate diagnostic", () => {
    const src = `/** @ensures{p} forall (x: int) { f(x) === x } */
/** @ensures{p} forall (x: int) { f(x) === x } */
export function f(x: number): number { return x; }
`;
    const r = extractFromSource(src, "stacked-dup.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.message).toContain("duplicate property name 'p'");
    expect(r.invalid[0]!.message).toContain("declared 2 times");
  });

  it("does not attach a block that belongs to the preceding declaration", () => {
    const src = `/** @ensures{first} forall (x: int) { a(x) === x } */
export function a(x: number): number { return x; }
/** @ensures{second} forall (x: int) { b(x) === x } */
export function b(x: number): number { return x; }
`;
    const r = extractFromSource(src, "neighbors.ts");
    expect(r.invalid).toEqual([]);
    expect(r.annotations.map((a) => [a.propertyName, a.functionName])).toEqual([
      ["first", "a"],
      ["second", "b"],
    ]);
  });
});
