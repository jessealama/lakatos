import { describe, it, expect, afterEach } from "vitest";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import {
  defaultBinary,
  defaultCheckout,
  findTarskiRoot,
  pinPath,
} from "../src/test262/paths.js";

const here = fileURLToPath(import.meta.url);

describe("findTarskiRoot", () => {
  it("finds the lake package from a file inside it", () => {
    const root = findTarskiRoot(here);
    expect(root).toBeDefined();
    expect(existsSync(path.join(root ?? "", "lakefile.lean"))).toBe(true);
  });

  // The installed copy's `dist/` is not under `tarski/`, so the walk has
  // to find the package as a *child* of an ancestor as well.
  it("finds the lake package from a sibling tree", () => {
    const root = findTarskiRoot(here);
    const repo = path.dirname(root ?? "");
    expect(
      findTarskiRoot(
        path.join(repo, "dist", "tarski", "frontend", "src", "x.js"),
      ),
    ).toBe(root);
  });

  it("is undefined where there is no lake package", () => {
    expect(
      findTarskiRoot(path.join(path.parse(here).root, "nothing-here.js")),
    ).toBeUndefined();
  });
});

describe("the default paths", () => {
  const previous = process.env.LAKATOS_TEST262;
  afterEach(() => {
    if (previous === undefined) delete process.env.LAKATOS_TEST262;
    else process.env.LAKATOS_TEST262 = previous;
  });

  it("puts the binary where lake build tarski does", () => {
    expect(defaultBinary("/r")).toBe(
      path.join("/r", ".lake", "build", "bin", "tarski"),
    );
  });

  it("puts the checkout in the ignored directory", () => {
    delete process.env.LAKATOS_TEST262;
    expect(defaultCheckout("/r")).toBe(path.join("/r", ".test262"));
  });

  it("prefers LAKATOS_TEST262 when it is set", () => {
    process.env.LAKATOS_TEST262 = "/elsewhere";
    expect(defaultCheckout("/r")).toBe("/elsewhere");
  });

  it("reads the pin from the package", () => {
    expect(pinPath("/r")).toBe(path.join("/r", "test262", "pin.json"));
  });
});
