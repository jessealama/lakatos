import { describe, it, expect } from "vitest";
import { classify } from "../src/free-idents.js";

describe("classify", () => {
  const bound = new Set(["x", "y"]);
  const exports = new Set(["foo"]);

  it("routes module exports to freeExports and ignores bound vars + globals", () => {
    const ids = new Set(["x", "y", "Math", "foo"]);
    expect(classify(ids, bound, exports)).toEqual({
      freeExports: ["foo"],
    });
  });

  it("throws on an unexported, non-global, non-bound identifier", () => {
    const ids = new Set(["x", "bar"]);
    // File and property name come from the per-annotation wrapper in
    // build-spec, so the message here names only the identifier.
    expect(() => classify(ids, bound, exports)).toThrow(
      "references 'bar', which is not exported",
    );
  });
});
