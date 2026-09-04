import { describe, it, expect } from "vitest";
import { domainCardinality, prefixCardinality } from "../src/cardinality.js";
import type { Binder } from "../src/binder.js";

const b = (domain: Binder["domain"], range?: Binder["range"]): Binder => ({
  varName: "x",
  domain,
  ...(range !== undefined ? { range } : {}),
});

describe("domainCardinality", () => {
  it("boolean has two values", () => {
    expect(domainCardinality(b("boolean"))).toBe(2n);
  });

  it("a bounded int interval is hi - lo + 1, open endpoints folded", () => {
    expect(domainCardinality(b("int", { min: "1", max: "10" }))).toBe(10n);
    expect(
      domainCardinality(b("int", { min: "0", max: "5", maxOpen: true })),
    ).toBe(5n);
    expect(domainCardinality(b("int", { min: "-3", max: "3" }))).toBe(7n);
    expect(
      domainCardinality(b("int", { min: "0", minOpen: true, max: "8" })),
    ).toBe(8n);
  });

  it("an int with an unbounded side is not enumerable", () => {
    expect(domainCardinality(b("int"))).toBeUndefined();
    expect(domainCardinality(b("int", { min: "0" }))).toBeUndefined();
    expect(domainCardinality(b("int", { max: "3" }))).toBeUndefined();
  });

  it("nat with only a ceiling is finite: the floor is 0", () => {
    expect(domainCardinality(b("nat", { max: "5" }))).toBe(6n);
    expect(domainCardinality(b("nat", { min: "-2", max: "5" }))).toBe(6n);
    expect(
      domainCardinality(b("nat", { minOpen: true, max: "5", maxOpen: true })),
    ).toBe(5n);
  });

  it("nat without a ceiling is not enumerable", () => {
    expect(domainCardinality(b("nat"))).toBeUndefined();
    expect(domainCardinality(b("nat", { min: "1" }))).toBeUndefined();
  });

  it("a bounded bigint interval counts like int", () => {
    expect(domainCardinality(b("bigint", { min: "0", max: "100" }))).toBe(101n);
    expect(
      domainCardinality(b("bigint", { min: "0", minOpen: true, max: "100" })),
    ).toBe(100n);
    expect(domainCardinality(b("bigint", { min: "0" }))).toBeUndefined();
    expect(domainCardinality(b("bigint"))).toBeUndefined();
  });

  it("keeps a count near the safe range exact", () => {
    expect(
      domainCardinality(
        b("int", { min: "9007199254740980", max: "9007199254740991" }),
      ),
    ).toBe(12n);
  });

  it("number is never enumerable, bounded or not", () => {
    expect(domainCardinality(b("number"))).toBeUndefined();
    expect(
      domainCardinality(b("number", { min: "0", max: "1" })),
    ).toBeUndefined();
    expect(
      domainCardinality(b("number", { min: "1", max: "1" })),
    ).toBeUndefined();
  });

  it("string is never enumerable, with or without a pattern", () => {
    expect(domainCardinality(b("string"))).toBeUndefined();
    expect(
      domainCardinality({
        varName: "s",
        domain: "string",
        pattern: { source: "[a-z]+", flags: "" },
      }),
    ).toBeUndefined();
  });

  it("a class binder is not enumerable", () => {
    expect(
      domainCardinality({
        varName: "p",
        domain: { className: "Point", ctorParams: [] },
      }),
    ).toBeUndefined();
  });
});

describe("prefixCardinality", () => {
  it("multiplies the binders", () => {
    expect(
      prefixCardinality([
        b("int", { min: "0", max: "10", maxOpen: true }),
        b("boolean"),
      ]),
    ).toBe(20n);
  });

  it("one non-enumerable binder makes the prefix non-enumerable", () => {
    expect(
      prefixCardinality([b("int", { min: "0", max: "9" }), b("number")]),
    ).toBeUndefined();
  });

  it("the empty product is one", () => {
    expect(prefixCardinality([])).toBe(1n);
  });
});
