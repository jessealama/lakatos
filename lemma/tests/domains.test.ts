import { describe, it, expect } from "vitest";
import {
  clampedEndpoints,
  intBounds,
  intInterval,
  MAX_SAFE,
  unsupportedRangeReason,
} from "../src/domains.js";

const HUGE = "1000000000000000000000000000000";

describe("intInterval", () => {
  it("folds open endpoints into inclusive ones", () => {
    expect(intInterval("int", { min: "0", max: "10", maxOpen: true })).toEqual({
      lo: 0n,
      hi: 9n,
    });
    expect(intInterval("int", { min: "0", minOpen: true, max: "10" })).toEqual({
      lo: 1n,
      hi: 10n,
    });
    expect(
      intInterval("int", {
        min: "0",
        minOpen: true,
        max: "10",
        maxOpen: true,
      }),
    ).toEqual({ lo: 1n, hi: 9n });
  });

  it("leaves an unbounded int side unbounded", () => {
    expect(intInterval("int", { min: "0" })).toEqual({ lo: 0n });
    expect(intInterval("int", { max: "3" })).toEqual({ hi: 3n });
    expect(intInterval("int", {})).toEqual({});
  });

  it("floors nat at 0 whether the written lower bound is negative or -∞", () => {
    expect(intInterval("nat", { min: "-2", max: "5" })).toEqual({
      lo: 0n,
      hi: 5n,
    });
    expect(intInterval("nat", { max: "5" })).toEqual({ lo: 0n, hi: 5n });
    expect(intInterval("nat", {})).toEqual({ lo: 0n });
    // The open-endpoint fold lands exactly on the floor, which must not
    // then shift it further.
    expect(intInterval("nat", { min: "-1", minOpen: true, max: "5" })).toEqual({
      lo: 0n,
      hi: 5n,
    });
  });

  it("keeps endpoints beyond the safe range exact", () => {
    expect(intInterval("int", { min: "0", max: HUGE })).toEqual({
      lo: 0n,
      hi: BigInt(HUGE),
    });
  });
});

describe("intBounds clamp reporting", () => {
  it("reports no clamping for an in-range interval", () => {
    const b = intBounds("int", { min: "0", max: "10" });
    expect(b).toEqual({
      lo: 0n,
      hi: 10n,
      clampedLo: false,
      clampedHi: false,
      rawLo: 0n,
      rawHi: 10n,
    });
  });

  it("flags an upper endpoint beyond the safe range and clamps it", () => {
    const b = intBounds("int", { min: "0", max: HUGE });
    expect(b.clampedLo).toBe(false);
    expect(b.clampedHi).toBe(true);
    expect(b.hi).toBe(MAX_SAFE);
  });

  it("flags a lower endpoint beyond the negative safe range and clamps it", () => {
    const b = intBounds("int", { min: `-${HUGE}`, max: "5" });
    expect(b.clampedLo).toBe(true);
    expect(b.clampedHi).toBe(false);
    expect(b.lo).toBe(-MAX_SAFE);
  });

  it("flags both endpoints when both fall outside the safe range", () => {
    const b = intBounds("int", { min: `-${HUGE}`, max: HUGE });
    expect(b.clampedLo).toBe(true);
    expect(b.clampedHi).toBe(true);
  });

  it("flags a lower endpoint beyond the positive safe range (empty result)", () => {
    const b = intBounds("int", { min: HUGE, max: `${HUGE}0` });
    expect(b.clampedLo).toBe(true);
    expect(b.clampedHi).toBe(true);
    expect(b.lo > b.hi).toBe(true);
  });

  it("a huge negative nat lower endpoint floors at 0 without clamping", () => {
    const b = intBounds("nat", { min: `-${HUGE}`, max: "5" });
    expect(b).toEqual({
      lo: 0n,
      hi: 5n,
      clampedLo: false,
      clampedHi: false,
      rawLo: 0n,
      rawHi: 5n,
    });
  });

  it("keeps the pre-clamp bounds so emptiness can be attributed", () => {
    const b = intBounds("int", { min: HUGE, max: `${HUGE}0` });
    expect(b.rawLo).toBe(BigInt(HUGE));
    expect(b.rawHi).toBe(BigInt(`${HUGE}0`));
    expect(b.rawLo <= b.rawHi).toBe(true);
  });
});

describe("clampedEndpoints", () => {
  it("reports nothing for a binder with no interval", () => {
    expect(clampedEndpoints({ varName: "n", domain: "int" })).toEqual([]);
  });

  it("reports nothing for a domain the clamp does not apply to", () => {
    for (const domain of ["number", "bigint"] as const) {
      expect(
        clampedEndpoints({ varName: "x", domain, range: { max: HUGE } }),
      ).toEqual([]);
    }
  });

  it("reports nothing for an interval inside the safe range", () => {
    expect(
      clampedEndpoints({
        varName: "n",
        domain: "int",
        range: { min: "0", max: "10" },
      }),
    ).toEqual([]);
  });

  it("names the ceiling when only it is beyond the safe range", () => {
    expect(
      clampedEndpoints({
        varName: "n",
        domain: "int",
        range: { min: "0", max: HUGE },
      }),
    ).toEqual([HUGE]);
  });

  it("names the floor when only it is beyond the safe range", () => {
    expect(
      clampedEndpoints({
        varName: "n",
        domain: "int",
        range: { min: `-${HUGE}`, max: "0" },
      }),
    ).toEqual([`-${HUGE}`]);
  });

  it("names both endpoints, floor first", () => {
    expect(
      clampedEndpoints({
        varName: "n",
        domain: "int",
        range: { min: `-${HUGE}`, max: HUGE },
      }),
    ).toEqual([`-${HUGE}`, HUGE]);
  });

  it("names both endpoints of an interval the clamp empties", () => {
    expect(
      clampedEndpoints({
        varName: "n",
        domain: "int",
        range: { min: HUGE, max: `${HUGE}0` },
      }),
    ).toEqual([HUGE, `${HUGE}0`]);
  });

  it("does not report an unbounded side: no endpoint was written", () => {
    expect(
      clampedEndpoints({ varName: "n", domain: "int", range: { min: "0" } }),
    ).toEqual([]);
    expect(
      clampedEndpoints({ varName: "n", domain: "int", range: { max: "0" } }),
    ).toEqual([]);
  });

  it("does not report nat's floor: flooring at 0 is not clamping", () => {
    expect(
      clampedEndpoints({
        varName: "n",
        domain: "nat",
        range: { min: `-${HUGE}`, max: "10" },
      }),
    ).toEqual([]);
  });
});

describe("unsupportedRangeReason", () => {
  it("agrees in number with one endpoint", () => {
    expect(unsupportedRangeReason([HUGE])).toBe(
      `endpoint ${HUGE} exceeds the safe integer range (±${MAX_SAFE})`,
    );
  });

  it("agrees in number with two", () => {
    expect(unsupportedRangeReason([`-${HUGE}`, HUGE])).toBe(
      `endpoints -${HUGE} and ${HUGE} exceed ` +
        `the safe integer range (±${MAX_SAFE})`,
    );
  });
});
