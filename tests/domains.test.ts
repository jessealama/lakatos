import { describe, expect, it } from "vitest";
import { arbitraryFor } from "../engines/pabst/src/domains.js";

describe("number binder domains", () => {
  it("samples the whole of binary64 when unguarded", () => {
    // The spec's answer: `number` denotes every binary64 value, NaN and the
    // infinities included. Bare fc.double() is exactly that.
    expect(arbitraryFor({ domain: "number" })).toBe("fc.double()");
  });

  it("excludes NaN once an interval guards the binder", () => {
    // NaN satisfies no interval, so a guarded binder must not sample it.
    // Range is { min?, max?, minOpen?, maxOpen? } — see lemma/src/binder.ts.
    const arb = arbitraryFor({
      domain: "number",
      range: { min: "0", max: "1" },
    });
    expect(arb).toContain("noNaN: true");
  });
});
