import { describe, it, expect } from "vitest";
import {
  argsTuple,
  ENUMERATION_CAP,
  enumerationCases,
  LOOP_BUDGET_MS,
  loopHeader,
  loopHeaders,
  TEST_TIMEOUT_MS,
} from "../src/enumerate.js";
import type { Binder } from "../src/ir.js";
import type { ClassCtorDomain } from "../../../lemma/src/index.js";

const int = (min: string, max: string, maxOpen = false): Binder => ({
  varName: "n",
  domain: "int",
  range: { min, max, ...(maxOpen ? { maxOpen: true } : {}) },
});

describe("enumerationCases", () => {
  it("counts a small domain as a number", () => {
    expect(enumerationCases([int("1", "10")])).toBe(10);
    expect(
      enumerationCases([
        int("0", "10", true),
        { varName: "b", domain: "boolean" },
      ]),
    ).toBe(20);
  });

  it("enumerates exactly at the cap and samples one above it", () => {
    expect(ENUMERATION_CAP).toBe(1000n);
    expect(enumerationCases([int("1", "1000")])).toBe(1000);
    expect(enumerationCases([int("0", "1000")])).toBeUndefined();
  });

  it("samples anything with a non-enumerable binder", () => {
    expect(enumerationCases([{ varName: "x", domain: "int" }])).toBeUndefined();
    expect(
      enumerationCases([int("0", "3"), { varName: "y", domain: "number" }]),
    ).toBeUndefined();
  });
});

describe("loopHeader", () => {
  it("walks int and nat ascending over the denoted interval", () => {
    expect(loopHeader(int("1", "10"))).toBe("for (let n = 1; n <= 10; n++) {");
    expect(loopHeader(int("0", "10", true))).toBe(
      "for (let n = 0; n <= 9; n++) {",
    );
    expect(
      loopHeader({
        varName: "k",
        domain: "nat",
        range: { min: "-2", minOpen: true, max: "5" },
      }),
    ).toBe("for (let k = 0; k <= 5; k++) {");
  });

  it("walks bigint with n-suffixed literals", () => {
    expect(
      loopHeader({
        varName: "b",
        domain: "bigint",
        range: { min: "0", minOpen: true, max: "100" },
      }),
    ).toBe("for (let b = 1n; b <= 100n; b++) {");
  });

  it("walks boolean false then true", () => {
    expect(loopHeader({ varName: "f", domain: "boolean" })).toBe(
      "for (const f of [false, true]) {",
    );
  });

  it("refuses a binder the cardinality helper would never admit", () => {
    expect(() => loopHeader({ varName: "x", domain: "number" })).toThrow(
      /not enumerable/,
    );
    expect(() => loopHeader({ varName: "n", domain: "int" })).toThrow(
      /not enumerable/,
    );
    expect(() =>
      loopHeader({ varName: "n", domain: "nat", range: { min: "0" } }),
    ).toThrow(/not enumerable/);
    expect(() =>
      loopHeader({ varName: "b", domain: "bigint", range: { min: "0" } }),
    ).toThrow(/not enumerable/);
    expect(() => loopHeader({ varName: "b", domain: "bigint" })).toThrow(
      /not enumerable/,
    );
    expect(() =>
      loopHeader({
        varName: "p",
        domain: {
          className: "Point",
          ctorParams: [{ name: "x", domain: "number" }],
        },
      }),
    ).toThrow(/not enumerable/);
  });

  it("refuses int endpoints a number literal could not denote", () => {
    expect(() =>
      loopHeader(int("9007199254740993", "9007199254740999")),
    ).toThrow(/outside the safe integer range/);
  });
});

const flagParams = [
  { name: "on", domain: "boolean" as const },
  { name: "armed", domain: "boolean" as const },
];
const flag: Binder = {
  varName: "f",
  domain: { className: "Flag", ctorParams: flagParams },
};
const pair: Binder = {
  varName: "p",
  domain: {
    className: "Pair",
    ctorParams: [
      { name: "a", domain: { className: "Flag", ctorParams: flagParams } },
      { name: "b", domain: { className: "Flag", ctorParams: flagParams } },
      { name: "tag", domain: "boolean" },
    ],
  },
};

describe("loopHeaders", () => {
  it("wraps a primitive binder's single loop", () => {
    expect(loopHeaders(int("1", "3"))).toEqual([
      "for (let n = 1; n <= 3; n++) {",
    ]);
  });

  it("opens one loop per constructor slot, in slot order", () => {
    expect(loopHeaders(flag)).toEqual([
      "for (const __f_0 of [false, true]) {",
      "for (const __f_1 of [false, true]) {",
    ]);
  });

  it("flattens a nested class slot depth first", () => {
    expect(loopHeaders(pair)).toEqual([
      "for (const __p_0_0 of [false, true]) {",
      "for (const __p_0_1 of [false, true]) {",
      "for (const __p_1_0 of [false, true]) {",
      "for (const __p_1_1 of [false, true]) {",
      "for (const __p_2 of [false, true]) {",
    ]);
  });

  it("opens no loop for a zero-argument constructor", () => {
    expect(
      loopHeaders({
        varName: "u",
        domain: { className: "Unit", ctorParams: [] },
      }),
    ).toEqual([]);
  });

  it("refuses a class whose constructor was never resolved", () => {
    const unresolved: Binder = { varName: "p", domain: { className: "Point" } };
    expect(() => loopHeaders(unresolved)).toThrow(/unresolved class binder/);
    expect(() => argsTuple("p", { className: "Point" })).toThrow(
      /unresolved class binder/,
    );
  });

  it("refuses a class with a slot the cardinality helper would never admit", () => {
    expect(() =>
      loopHeaders({
        varName: "c",
        domain: {
          className: "C",
          ctorParams: [{ name: "s", domain: "string" }],
        },
      }),
    ).toThrow(/not enumerable/);
  });
});

describe("argsTuple", () => {
  it("rebuilds the constructor tuple from the leaf loop variables", () => {
    const domainOf = (b: Binder) => b.domain as ClassCtorDomain;
    expect(argsTuple("f", domainOf(flag))).toBe("[__f_0, __f_1]");
    expect(argsTuple("p", domainOf(pair))).toBe(
      "[[__p_0_0, __p_0_1], [__p_1_0, __p_1_1], __p_2]",
    );
    expect(argsTuple("u", { className: "Unit", ctorParams: [] })).toBe("[]");
  });
});

describe("the budget constants", () => {
  it("keep the vitest timeout above the loop budget", () => {
    // vitest's timer cannot interrupt a synchronous loop; the loop must
    // give up first so its budget issue, not a bare timeout, is reported.
    expect(TEST_TIMEOUT_MS).toBeGreaterThan(LOOP_BUDGET_MS);
  });
});
