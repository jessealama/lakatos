import { describe, it, expect } from "vitest";
import { extractFromSource } from "../src/extract.js";

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
    expect(i.message).toMatch(/non-public method 'touch'/);
  });

  it("collects @ensures on an accessor as invalid", () => {
    const r = extractFromSource(CLASS_ACCESSOR, "class-accessor.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.functionName).toBe("value");
    expect(r.invalid[0]!.message).toMatch(/unsupported member 'value'/);
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
      /duplicate property name 'p' on method 'Box\.id'/,
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
    expect(r.invalid[0]!.message).toMatch(/non-public method 'touch'/);
    expect(r.invalid[1]!.message).toMatch(/unsupported member 'probe'/);
  });

  it("ignores an @ensures tag without a {name} prefix", () => {
    const src = `/** @ensures forall (x: int) { f(x) === x } */
/** @ensures */
export function f(x: number): number { return x; }
`;
    const r = extractFromSource(src, "unnamed.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toEqual([]);
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
    expect(r.invalid[0]!.message).toMatch(/non-public method '#hidden'/);
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

  it("collects @ensures on a constructor as invalid, labeled 'constructor'", () => {
    const src = `export class Box {
  /** @ensures{p} forall (x: int) { x === x } */
  constructor(readonly n: number) {}
}
`;
    const r = extractFromSource(src, "ctor.ts");
    expect(r.annotations).toEqual([]);
    expect(r.invalid).toHaveLength(1);
    expect(r.invalid[0]!.functionName).toBe("constructor");
    expect(r.invalid[0]!.message).toMatch(/unsupported member 'constructor'/);
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
