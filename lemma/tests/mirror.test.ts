import { describe, expect, test } from "vitest";
import * as path from "node:path";
import { LemmaError } from "../src/errors.js";
import { mirrorPath } from "../src/mirror.js";

describe("mirrorPath", () => {
  test("mirrors the relative path under the out root, extension kept", () => {
    expect(mirrorPath(path.join("sub", "a.ts"), "out", ".lean")).toBe(
      path.join("out", "sub", "a.ts.lean"),
    );
  });

  test("sources differing only by extension map to distinct out-files", () => {
    const outs = ["x.ts", "x.tsx", "x.mts", "x.cts"].map((f) =>
      mirrorPath(f, "out", ".pabst.test.ts"),
    );
    expect(new Set(outs).size).toBe(outs.length);
  });

  test("resolves an absolute path inside cwd to its relative mirror", () => {
    expect(mirrorPath(path.resolve("a.ts"), "out", ".lean")).toBe(
      path.join("out", "a.ts.lean"),
    );
  });

  test("refuses sources outside the current directory", () => {
    expect(() =>
      mirrorPath(path.join("..", "nope.ts"), "out", ".lean"),
    ).toThrow(LemmaError);
  });
});
