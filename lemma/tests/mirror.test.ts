import { describe, expect, test } from "vitest";
import * as path from "node:path";
import { LemmaError } from "../src/errors.js";
import { mirrorPath } from "../src/mirror.js";

describe("mirrorPath", () => {
  test("mirrors the relative path under the out root, extension kept", () => {
    expect(mirrorPath(path.join("sub", "a.ts"), ".thales", ".lean")).toBe(
      path.join(".thales", "sub", "a.ts.lean"),
    );
  });

  test("sources differing only by extension map to distinct out-files", () => {
    const outs = ["x.ts", "x.tsx", "x.mts", "x.cts"].map((f) =>
      mirrorPath(f, ".pabst", ".pabst.test.ts"),
    );
    expect(new Set(outs).size).toBe(outs.length);
  });

  test("resolves an absolute path inside cwd to its relative mirror", () => {
    expect(mirrorPath(path.resolve("a.ts"), ".thales", ".lean")).toBe(
      path.join(".thales", "a.ts.lean"),
    );
  });

  test("refuses sources outside the current directory", () => {
    expect(() =>
      mirrorPath(path.join("..", "nope.ts"), ".thales", ".lean"),
    ).toThrow(LemmaError);
  });
});
