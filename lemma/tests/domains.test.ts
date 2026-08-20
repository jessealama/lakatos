import { describe, it, expect } from "vitest";
import { intBounds, MAX_SAFE } from "../src/domains.js";

const HUGE = "1000000000000000000000000000000";

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
