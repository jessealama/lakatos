import { describe, it, expect } from "vitest";
import {
  ENUMERATION_CAP,
  enumerationCases,
  LOOP_BUDGET_MS,
  loopHeader,
  TEST_TIMEOUT_MS,
} from "../src/enumerate.js";
import type { Binder } from "../src/ir.js";

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
});

describe("the budget constants", () => {
  it("keep the vitest timeout above the loop budget", () => {
    // vitest's timer cannot interrupt a synchronous loop; the loop must
    // give up first so its budget issue, not a bare timeout, is reported.
    expect(TEST_TIMEOUT_MS).toBeGreaterThan(LOOP_BUDGET_MS);
  });
});
