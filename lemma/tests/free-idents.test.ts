import { describe, it, expect } from "vitest";
import { freeIdentifiers } from "../src/free-idents.js";

describe("freeIdentifiers", () => {
  it("collects references but not property names", () => {
    const ids = freeIdentifiers("Number.isInteger(y) && foo(x, y) !== 0");
    expect([...ids].sort()).toEqual(["Number", "foo", "x", "y"]);
  });

  it("excludes object-literal keys but keeps value refs", () => {
    const ids = freeIdentifiers("({ a: x }).a === x");
    expect([...ids].sort()).toEqual(["x"]);
  });

  it("excludes the right side of a qualified type name", () => {
    // In `x as Foo.Bar`, `Bar` is the right of a qualified name and must be
    // dropped; `Foo` (the left) and `x` remain.
    const ids = freeIdentifiers("x as Foo.Bar");
    expect([...ids].sort()).toEqual(["Foo", "x"]);
  });
});
