import { describe, it, expect, vi } from "vitest";
import { runMain, useTempProject } from "./helpers/cli.js";

// The stub's enumeration wraps LemmaErrors with the annotation's location,
// the same seam build-spec uses. An internal bug must still crash loudly
// rather than be dressed up as a compile error, so simulate one by making
// the prefix parser throw a TypeError.
vi.mock("../lemma/src/prefix-parser.js", () => ({
  parsePrefix: () => {
    throw new TypeError("internal invariant violated");
  },
}));

describe("check stub internal errors", () => {
  useTempProject("lakatos-cli-stub-internal-", {
    "fine.ts": `/** @ensures{pos} forall (n: nat) { fine(n) >= 0 } */\nexport function fine(n: number): number { return n; }\n`,
  });

  it("a non-LemmaError from enumeration escapes main() instead of exiting 2", () => {
    expect(() => runMain(["check", "fine.ts"])).toThrow(TypeError);
  });
});
