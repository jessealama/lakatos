import { describe, it, expect } from "vitest";
import { extractFromSource } from "../src/extract.js";
import { parsePrefix } from "../src/prefix-parser.js";
import { resolveClassBinders } from "../src/class-domain.js";
import type { Binder } from "../src/binder.js";
import { expectLemmaError } from "./helpers/errors.js";

/** Parse a prefix and resolve its class binders against a module. */
function resolve(src: string, formula: string, file = "mod.ts"): Binder[] {
  const { classes } = extractFromSource(src, file);
  const { binders } = parsePrefix(formula);
  resolveClassBinders(binders, classes, file);
  return binders;
}

const POINT = `
export class Point {
  public readonly x: number;
  public readonly y: number;
  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }
}
`;

describe("resolveClassBinders", () => {
  it("attaches constructor parameters to a resolved class binder", () => {
    const binders = resolve(POINT, "forall (p q: Point) { p === q }");
    const expected = {
      className: "Point",
      ctorParams: [
        { name: "x", domain: "number" },
        { name: "y", domain: "number" },
      ],
    };
    expect(binders[0]!.domain).toEqual(expected);
    expect(binders[1]!.domain).toEqual(expected);
  });

  it("accepts every generable primitive as a parameter type", () => {
    const src = `
export class Tag {
  constructor(name: string, count: bigint, active: boolean, n: number) {}
}
`;
    const [b] = resolve(src, "forall (t: Tag) { t === t }");
    expect(b!.domain).toEqual({
      className: "Tag",
      ctorParams: [
        { name: "name", domain: "string" },
        { name: "count", domain: "bigint" },
        { name: "active", domain: "boolean" },
        { name: "n", domain: "number" },
      ],
    });
  });

  it("accepts parameter properties", () => {
    const src = `export class Counter { constructor(readonly n: number) {} }`;
    const [b] = resolve(src, "forall (c: Counter) { c === c }");
    expect(b!.domain).toEqual({
      className: "Counter",
      ctorParams: [{ name: "n", domain: "number" }],
    });
  });

  it("accepts a class with no constructor (empty image basis)", () => {
    const src = `export class Unit {}`;
    const [b] = resolve(src, "forall (u: Unit) { u === u }");
    expect(b!.domain).toEqual({ className: "Unit", ctorParams: [] });
  });

  it("leaves primitive binders untouched", () => {
    const binders = resolve(POINT, "forall (p: Point) (k: number) { p === k }");
    expect(binders[1]!.domain).toBe("number");
  });

  it("rejects a domain that names no class", () => {
    expectLemmaError(
      () => resolve(POINT, "forall (x: float) { x === x }"),
      /domain 'float' is neither a primitive domain \(int, nat, number, boolean, string, bigint\) nor an exported class declared in mod\.ts/,
    );
  });

  it("rejects a non-exported class", () => {
    const src = `class Hidden { constructor(v: number) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (h: Hidden) { h === h }"),
      /class 'Hidden' is not exported from mod\.ts/,
    );
  });

  it("rejects a default-exported class", () => {
    const src = `export default class Point { constructor(x: number) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (p: Point) { p === p }"),
      /class 'Point' is default-exported from mod\.ts; a binder domain needs a named export/,
    );
  });

  it("rejects an optional constructor parameter, naming it", () => {
    const src = `export class Offset { constructor(x: number, y?: number) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (o: Offset) { o === o }"),
      /constructor parameter 'y' is optional/,
    );
  });

  it("accepts a defaulted constructor parameter at full arity", () => {
    const src = `export class Offset { constructor(x: number, y: number = 0) {} }`;
    const [b] = resolve(src, "forall (o: Offset) { o === o }");
    expect(b!.domain).toEqual({
      className: "Offset",
      ctorParams: [
        { name: "x", domain: "number" },
        { name: "y", domain: "number" },
      ],
    });
  });

  it("rejects a defaulted parameter with no type annotation", () => {
    const src = `export class Offset { constructor(x: number, y = 0) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (o: Offset) { o === o }"),
      /constructor parameter 'y' has no type annotation/,
    );
  });

  it("rejects a rest constructor parameter, naming it", () => {
    const src = `export class Path { constructor(...xs: number[]) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (p: Path) { p === p }"),
      /constructor parameter 'xs' is a rest parameter/,
    );
  });

  it("rejects a union-typed constructor parameter, naming the type", () => {
    const src = `export class Label { constructor(text: string | number) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (l: Label) { l === l }"),
      /constructor parameter 'text' has type 'string \| number' — constructor parameters must be annotated number, boolean, string, or bigint/,
    );
  });

  it("rejects a class-typed constructor parameter", () => {
    const src = `
export class Anchor { constructor(x: number) {} }
export class Rope { constructor(from: Anchor) {} }
`;
    expectLemmaError(
      () => resolve(src, "forall (r: Rope) { r === r }"),
      /constructor parameter 'from' has type 'Anchor'/,
    );
  });

  it("rejects an unannotated constructor parameter", () => {
    const src = `export class Loose { constructor(x) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (l: Loose) { l === l }"),
      /constructor parameter 'x' has no type annotation/,
    );
  });

  it("rejects an overloaded constructor", () => {
    const src = `
export class Multi {
  constructor(x: number);
  constructor(x: number, y: number);
  constructor(x: number, y?: number) {}
}
`;
    expectLemmaError(
      () => resolve(src, "forall (m: Multi) { m === m }"),
      /overloaded constructor/,
    );
  });

  it("rejects a destructured constructor parameter", () => {
    const src = `export class Vec { constructor({ x }: { x: number }) {} }`;
    expectLemmaError(
      () => resolve(src, "forall (v: Vec) { v === v }"),
      /constructor parameter is destructured/,
    );
  });
});
