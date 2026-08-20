import { describe, it, expect, vi } from "vitest";
import { runMain, useTempProject } from "./helpers/cli.js";

// Only user-facing compile errors map to exit 2. An internal bug (anything
// that is not a LemmaError) must keep crashing loudly rather than being
// dressed up as a usage error. A real internal bug can't be triggered on
// purpose, so simulate one by making the generator throw a TypeError.
vi.mock("../engines/pabst/src/codegen.js", () => ({
  generate: () => {
    throw new TypeError("internal invariant violated");
  },
}));

describe("cli internal errors", () => {
  useTempProject("lakatos-cli-internal-", {
    "fine.ts": `/** @ensures{pos} forall (n: nat) { fine(n) >= 0 } */\nexport function fine(n: number): number { return n; }\n`,
  });

  it("a non-LemmaError from compilation escapes main() instead of exiting 2", () => {
    expect(() => runMain(["refute", "fine.ts"])).toThrow(TypeError);
  });
});
