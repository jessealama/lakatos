import { describe, expect, it } from "vitest";
import { stripTypes } from "../src/strip-types.js";

// tsc's own printing is pinned as text rather than described, so that a
// tsc upgrade that changes the emit is caught here — where it reads as one
// diff — rather than in a fixture run against the evaluator.
describe("stripTypes", () => {
  it("erases the example's types and leaves the program as tsc prints it", () => {
    const source =
      'export function inv(x: number): number { if (x === 0) throw new RangeError("zero"); return 1 / x; }\n' +
      "console.log(inv(4));\n" +
      "console.log(inv(0));\n";
    expect(stripTypes(source, "foo.ts")).toBe(
      '"use strict";\n' +
        "function inv(x) { if (x === 0)\n" +
        '    throw new RangeError("zero"); return 1 / x; }\n' +
        "console.log(inv(4));\n" +
        "console.log(inv(0));\n",
    );
  });

  it("strips export and default from a declaration", () => {
    expect(stripTypes("export default class Foo {}", "t.ts")).toBe(
      '"use strict";\nclass Foo {\n}\n',
    );
    expect(stripTypes("export const k = 2;", "t.ts")).toBe(
      '"use strict";\nconst k = 2;\n',
    );
    expect(stripTypes("export function f(): void {}", "t.ts")).toBe(
      '"use strict";\nfunction f() { }\n',
    );
  });

  it("drops an export declaration, which has no effect on a run", () => {
    expect(stripTypes("const a = 1;\nexport { a };", "t.ts")).toBe(
      '"use strict";\nconst a = 1;\n',
    );
    expect(stripTypes('export * from "./x.js";', "t.ts")).toBe(
      '"use strict";\n',
    );
  });

  it("evaluates an export assignment in place", () => {
    expect(stripTypes("export default 1 + 1;", "t.ts")).toBe(
      '"use strict";\n1 + 1;\n',
    );
  });

  it("erases a type-only declaration", () => {
    expect(stripTypes("export type T = number;\nconst x: T = 1;", "t.ts")).toBe(
      '"use strict";\nconst x = 1;\n',
    );
  });

  // Left in place on purpose: `exe` resolves no module graph, and the
  // bridge refusing an ImportDeclaration by name is a better report than a
  // binding that silently vanished.
  it("leaves an import declaration for the bridge to refuse", () => {
    expect(stripTypes('import { g } from "./g.js";\ng();', "t.ts")).toBe(
      '"use strict";\nimport { g } from "./g.js";\ng();\n',
    );
  });

  it("adds the strict directive, and only one of it", () => {
    expect(stripTypes("let x: number = 1;", "t.ts")).toBe(
      '"use strict";\nlet x = 1;\n',
    );
    expect(stripTypes('"use strict";\nlet x = 1;', "t.ts")).toBe(
      '"use strict";\nlet x = 1;\n',
    );
  });

  // A module gets no `export {}` tail: the transformer runs after tsc has
  // decided the file is a module, so nothing re-marks it.
  it("leaves no module marker behind", () => {
    expect(stripTypes("export const k = 2;", "t.ts")).not.toContain("export");
  });

  it("lowers a parameter property to a field and an assignment", () => {
    expect(
      stripTypes(
        "class C { constructor(private readonly n: number) {} }",
        "t.ts",
      ),
    ).toBe(
      '"use strict";\nclass C {\n    n;\n    constructor(n) {\n        this.n = n;\n    }\n}\n',
    );
  });

  it("lowers an enum to a var and an IIFE", () => {
    expect(stripTypes("enum E { A, B }", "t.ts")).toBe(
      '"use strict";\nvar E;\n(function (E) {\n' +
        '    E[E["A"] = 0] = "A";\n' +
        '    E[E["B"] = 1] = "B";\n' +
        "})(E || (E = {}));\n",
    );
  });
});
