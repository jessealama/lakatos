import { describe, it, expect } from "vitest";
import { parseFrontMatter } from "../src/test262/frontmatter.js";

// The shapes here are taken from the suite at the pinned commit: flow
// lists in most files and block lists in a few hundred, `negative` a
// two-key map, `info` and `description` block scalars holding prose that
// happens to contain colons.
const wrap = (body: string): string =>
  `// Copyright (C) 2026\n/*---\n${body}---*/\nvar x = 1;\n`;

describe("parseFrontMatter", () => {
  it("reads a flow list", () => {
    expect(
      parseFrontMatter(wrap("includes: [propertyHelper.js, compareArray.js]\n"))
        .includes,
    ).toEqual(["propertyHelper.js", "compareArray.js"]);
  });

  it("reads a flow list written without spaces", () => {
    expect(parseFrontMatter(wrap("includes: [a.js,b.js]\n")).includes).toEqual([
      "a.js",
      "b.js",
    ]);
  });

  it("reads a block list", () => {
    const front = parseFrontMatter(
      wrap("features:\n  - Symbol\n  - Proxy\nflags: [onlyStrict]\n"),
    );
    expect(front.features).toEqual(["Symbol", "Proxy"]);
    expect(front.flags).toEqual(["onlyStrict"]);
  });

  it("reads the negative map", () => {
    expect(
      parseFrontMatter(wrap("negative:\n  phase: parse\n  type: SyntaxError\n"))
        .negative,
    ).toEqual({
      phase: "parse",
      type: "SyntaxError",
    });
  });

  it("has no negative when the block is absent", () => {
    expect(parseFrontMatter(wrap("flags: [async]\n")).negative).toBeUndefined();
  });

  it("stops a block list at the first line that is not an item", () => {
    const front = parseFrontMatter(
      wrap(
        "features:\n  - Symbol\n  note: not an item\n  - Proxy\nflags: [async]\n",
      ),
    );
    expect(front.features).toEqual(["Symbol"]);
    expect(front.flags).toEqual(["async"]);
  });

  it("ignores a negative block missing the phase", () => {
    expect(
      parseFrontMatter(wrap("negative:\n  type: SyntaxError\n")).negative,
    ).toBeUndefined();
  });

  it("ignores a line under negative that is not an entry", () => {
    expect(
      parseFrontMatter(
        wrap("negative:\n  - phase\n  phase: parse\n  type: SyntaxError\n"),
      ).negative,
    ).toEqual({ phase: "parse", type: "SyntaxError" });
  });

  it("ignores a negative block missing a key", () => {
    expect(
      parseFrontMatter(wrap("negative:\n  phase: parse\n")).negative,
    ).toBeUndefined();
  });

  // A block scalar is prose. Its lines are indented, so the key scan at
  // column 0 never sees them — which is what lets `info` contain
  // anything, including something that looks like a key.
  it("skips block scalars", () => {
    const front = parseFrontMatter(
      wrap(
        [
          "description: >",
          "  A description that wraps",
          "  onto a second line",
          "info: |",
          "  flags: [raw]",
          "  includes: [nope.js]",
          "includes: [real.js]",
          "",
        ].join("\n"),
      ),
    );
    expect(front.includes).toEqual(["real.js"]);
    expect(front.flags).toEqual([]);
  });

  it("drops a trailing comment", () => {
    const front = parseFrontMatter(
      wrap("flags: [async] # not run here\nfeatures:\n  - Symbol # es6\n"),
    );
    expect(front.flags).toEqual(["async"]);
    expect(front.features).toEqual(["Symbol"]);
  });

  it("reads an empty flow list as empty", () => {
    expect(parseFrontMatter(wrap("flags: []\n")).flags).toEqual([]);
  });

  it("answers empty for a file with no front matter", () => {
    expect(parseFrontMatter("var x = 1;\n")).toEqual({
      includes: [],
      flags: [],
      features: [],
    });
  });

  it("answers empty for an unterminated block", () => {
    expect(parseFrontMatter("/*---\nflags: [async]\n")).toEqual({
      includes: [],
      flags: [],
      features: [],
    });
  });

  it("returns only the four keys it reads", () => {
    const front = parseFrontMatter(
      wrap(
        "esid: sec-assert\ndescription: a test\nauthor: someone\nincludes: [a.js]\n",
      ),
    );
    expect(Object.keys(front).sort()).toEqual([
      "features",
      "flags",
      "includes",
    ]);
  });
});
