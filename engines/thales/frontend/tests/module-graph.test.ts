import { describe, expect, test } from "vitest";
import * as path from "node:path";
import {
  type ModuleReader,
  modelKey,
  moduleQualifier,
  resolveImport,
} from "../src/module-graph.js";

/** An in-memory module tree, keyed the way the walk resolves: absolute
 * paths against the importing file's directory. */
function reader(files: Record<string, string>): ModuleReader {
  const abs = new Map(
    Object.entries(files).map(([f, text]) => [path.resolve(f), text]),
  );
  return (file) => abs.get(file);
}

describe("resolveImport", () => {
  test("a bare specifier resolves to nothing", () => {
    expect(resolveImport("node:fs", "main.ts", reader({}))).toBeUndefined();
    expect(resolveImport("lodash", "main.ts", reader({}))).toBeUndefined();
  });

  test("a relative specifier reaching no file resolves to nothing", () => {
    expect(resolveImport("./gone.js", "main.ts", reader({}))).toBeUndefined();
  });

  test("nodeNext spellings resolve to their TypeScript source", () => {
    const cases: Array<[string, string]> = [
      ["./helper.mjs", "helper.mts"],
      ["./helper.cjs", "helper.cts"],
      ["./helper.js", "helper.ts"],
    ];
    for (const [specifier, source] of cases) {
      const got = resolveImport(
        specifier,
        "main.ts",
        reader({ [source]: "x" }),
      );
      expect(got?.file).toBe(path.resolve(source));
      expect(got?.text).toBe("x");
    }
  });

  test("a .js specifier falls back to .tsx", () => {
    const got = resolveImport(
      "./view.js",
      "main.ts",
      reader({ "view.tsx": "x" }),
    );
    expect(got?.file).toBe(path.resolve("view.tsx"));
  });

  test("the TypeScript source wins over a sibling spelled as the specifier", () => {
    const got = resolveImport(
      "./helper.js",
      "main.ts",
      reader({ "helper.ts": "source", "helper.js": "emitted" }),
    );
    expect(got?.text).toBe("source");
  });

  test("a specifier resolves against the importing file's directory", () => {
    const got = resolveImport(
      "../shared/util.js",
      path.resolve("src/deep/main.ts"),
      reader({ "src/shared/util.ts": "x" }),
    );
    expect(got?.file).toBe(path.resolve("src/shared/util.ts"));
  });
});

describe("moduleQualifier", () => {
  test("is the dependency's path relative to the entry, posix-spelled", () => {
    expect(
      moduleQualifier(path.resolve("src"), path.resolve("src/helper.mts")),
    ).toBe("helper.mts");
    expect(
      moduleQualifier(path.resolve("src"), path.resolve("src/a/b/deep.ts")),
    ).toBe("a/b/deep.ts");
    expect(
      moduleQualifier(path.resolve("src"), path.resolve("shared/up.ts")),
    ).toBe("../shared/up.ts");
  });
});

describe("modelKey", () => {
  test("separates module from name with a character neither can contain", () => {
    expect(modelKey({ module: "helper.mts", name: "double" })).toBe(
      "helper.mts\0double",
    );
    expect(modelKey({ module: "", name: "twice" })).toBe("\0twice");
  });

  test("a module path and a class qualification cannot collide", () => {
    // Module `helper.mts` holding `x` versus class `helper` with static
    // member `mts` — the same string under any `.`-joined scheme.
    expect(modelKey({ module: "helper.mts", name: "x" })).not.toBe(
      modelKey({ module: "", name: "helper.mts.x" }),
    );
  });
});
