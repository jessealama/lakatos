import { assert, describe, expect, test } from "vitest";
import * as path from "node:path";
import { emitModule } from "../src/emission.js";
import { type ModuleReader } from "../src/module-graph.js";

/** An in-memory module tree, keyed the way the walk resolves: absolute
 * paths against the importing file's directory. */
function reader(files: Record<string, string>): ModuleReader {
  const abs = new Map(
    Object.entries(files).map(([f, text]) => [path.resolve(f), text]),
  );
  return (file) => abs.get(file);
}

const TWICE = [
  'import { double } from "./helper.mjs";',
  "/** @ensures{quadruples} forall (x: int ∈ [0, 20)) { twice(x) === 4 * x } */",
  "export function twice(x: number): number {",
  "  return double(x) + double(x);",
  "}",
  "",
].join("\n");

const HELPER = [
  "export function double(x: number): number {",
  "  return x * 2;",
  "}",
  "",
].join("\n");

describe("emission import closures", () => {
  test("a dependency is emitted under its module, before its user", () => {
    const { emission, classified } = emitModule(
      TWICE,
      "main.mts",
      reader({ "helper.mts": HELPER }),
    );
    expect(classified).toEqual([]);
    expect(emission.declarations.map((d) => [d.module, d.name])).toEqual([
      ["helper.mts", "double"],
      [undefined, "twice"],
    ]);
  });

  test("a call into a dependency carries the dependency's module", () => {
    const { emission } = emitModule(
      TWICE,
      "main.mts",
      reader({ "helper.mts": HELPER }),
    );
    const twice = emission.declarations.find((d) => d.name === "twice")!;
    assert(twice.kind === "function");
    const ret = twice.body[0]!;
    expect(ret.kind).toBe("return");
    expect(JSON.stringify(ret)).toContain('"module":"helper.mts"');
  });

  test("an imported class builds instances under its own module", () => {
    const boxed = [
      'import { Box } from "./box.mjs";',
      "/** @ensures{keeps} forall (x: number) { Object.is(new Box(x).v, x) } */",
      "export function keep(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const box = [
      "export class Box {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(
      boxed,
      "main.mts",
      reader({ "box.mts": box }),
    );
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toEqual({
      kind: "structured",
      binders: [{ name: "x", kind: "number" }],
      conclusion: {
        kind: "eq",
        left: {
          kind: "getter-read",
          className: "Box",
          module: "box.mts",
          name: "v",
          object: {
            kind: "new",
            className: "Box",
            module: "box.mts",
            args: [{ kind: "id", name: "x" }],
          },
        },
        right: { kind: "id", name: "x" },
      },
    });
  });

  test("a binder over an imported class carries the class's module", () => {
    const boxed = [
      'import { Box } from "./box.mjs";',
      "/** @ensures{nn} forall (b: Box) { b.v >= 0 } */",
      "export function keep(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const box = [
      "export class Box {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(
      boxed,
      "main.mts",
      reader({ "box.mts": box }),
    );
    expect(classified).toEqual([]);
    const payload = emission.obligations[0]!.payload;
    assert(payload.kind === "structured");
    expect(payload.binders).toEqual([
      {
        name: "b",
        kind: "class",
        className: "Box",
        module: "box.mts",
        ctorParams: ["v"],
      },
    ]);
  });

  test("a method call on an imported class carries its module", () => {
    const boxed = [
      'import { Dep } from "./dep.mjs";',
      "/** @ensures{keeps} forall (x: number) { Object.is(new Dep(x).m(), x) } */",
      "export function keep(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const dep = [
      "export class Dep {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  m(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(
      boxed,
      "main.mts",
      reader({ "dep.mts": dep }),
    );
    expect(classified).toEqual([]);
    expect(emission.obligations[0]!.payload).toEqual({
      kind: "structured",
      binders: [{ name: "x", kind: "number" }],
      conclusion: {
        kind: "eq",
        left: {
          kind: "method-call",
          className: "Dep",
          module: "dep.mts",
          name: "m",
          object: {
            kind: "new",
            className: "Dep",
            module: "dep.mts",
            args: [{ kind: "id", name: "x" }],
          },
          args: [],
        },
        right: { kind: "id", name: "x" },
      },
    });
  });

  test("a dependency's this-call carries the dependency's module", () => {
    const boxed = [
      'import { Dep } from "./dep.mjs";',
      "/** @ensures{keeps} forall (x: number) { Object.is(new Dep(x).twice(), x + x) } */",
      "export function keep(x: number): number {",
      "  return x;",
      "}",
      "",
    ].join("\n");
    const dep = [
      "export class Dep {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  base(): number {",
      "    return this.#v;",
      "  }",
      "  twice(): number {",
      "    return this.base() + this.base();",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(
      boxed,
      "main.mts",
      reader({ "dep.mts": dep }),
    );
    expect(classified).toEqual([]);
    const cls = emission.declarations[0]!;
    assert(cls.kind === "class");
    expect(cls.methods[1]!.body[0]).toMatchObject({
      kind: "return",
      expr: {
        left: {
          kind: "method-call",
          className: "Dep",
          module: "dep.mts",
          name: "base",
          object: { kind: "self" },
        },
      },
    });
  });

  test("only the entry's annotations become obligations", () => {
    const annotated = [
      "/** @ensures{pos} forall (x: int ∈ [0, 5)) { double(x) >= 0 } */",
      "export function double(x: number): number {",
      "  return x * 2;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(
      TWICE,
      "main.mts",
      reader({ "helper.mts": annotated }),
    );
    expect(emission.obligations.map((o) => o.function)).toEqual(["twice"]);
  });

  test("the closure is transitive and each module is emitted once", () => {
    const mid = [
      'import { base } from "./base.js";',
      "export function double(x: number): number {",
      "  return base(x) + base(x);",
      "}",
      "",
    ].join("\n");
    const base = "export function base(x: number): number {\n  return x;\n}\n";
    const { emission } = emitModule(
      TWICE,
      "main.mts",
      reader({ "helper.mts": mid, "base.ts": base }),
    );
    expect(emission.declarations.map((d) => [d.module, d.name])).toEqual([
      ["base.ts", "base"],
      ["helper.mts", "double"],
      [undefined, "twice"],
    ]);
  });

  test("a module two importers reach is walked once", () => {
    const entry = [
      'import { a } from "./a.js";',
      'import { b } from "./b.js";',
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { both(x) >= 0 } */",
      "export function both(x: number): number {",
      "  return a(x) + b(x);",
      "}",
      "",
    ].join("\n");
    const via = (name: string) =>
      [
        'import { base } from "./base.js";',
        `export function ${name}(x: number): number {`,
        "  return base(x);",
        "}",
        "",
      ].join("\n");
    const { emission, classified } = emitModule(
      entry,
      "main.mts",
      reader({
        "a.ts": via("a"),
        "b.ts": via("b"),
        "base.ts":
          "export function base(x: number): number {\n  return x;\n}\n",
      }),
    );
    expect(classified).toEqual([]);
    expect(emission.declarations.map((d) => [d.module, d.name])).toEqual([
      ["base.ts", "base"],
      ["a.ts", "a"],
      ["b.ts", "b"],
      [undefined, "both"],
    ]);
  });

  test("a specifier that is not a string literal degrades its bindings", () => {
    // Parse recovery admits one: the specifier is typed as an expression.
    const src = TWICE.replace('"./helper.mjs"', "`./helper.mjs`");
    const { classified } = emitModule(
      src,
      "main.mts",
      reader({ "helper.mts": HELPER }),
    );
    expect(classified[0]?.szs).toBe("Inappropriate");
    expect(classified[0]?.reason).toContain("ImportDeclaration");
  });

  test("an aliased import rewrites to the exported name", () => {
    const src = TWICE.replace(
      'import { double } from "./helper.mjs";',
      'import { double as twofold } from "./helper.mjs";',
    ).replace(/double\(x\)/g, "twofold(x)");
    const { emission, classified } = emitModule(
      src,
      "main.mts",
      reader({ "helper.mts": HELPER }),
    );
    expect(classified).toEqual([]);
    expect(JSON.stringify(emission)).toContain('"callee":"double"');
  });

  test("a bare specifier still degrades its bindings", () => {
    const src = TWICE.replace('"./helper.mjs"', '"lodash"');
    const { classified } = emitModule(src, "main.mts", reader({}));
    expect(classified[0]?.szs).toBe("Inappropriate");
    expect(classified[0]?.reason).toContain("ImportDeclaration");
  });

  test("a relative specifier reaching no file degrades its bindings", () => {
    const { classified } = emitModule(TWICE, "main.mts", reader({}));
    expect(classified[0]?.szs).toBe("Inappropriate");
    expect(classified[0]?.reason).toContain("ImportDeclaration");
  });

  test("an import cycle degrades the cycle-closing name, not the entry's own", () => {
    const cyclic = [
      'import { twice } from "./main.mjs";',
      "export function double(x: number): number {",
      "  return twice(x);",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(
      TWICE,
      "main.mts",
      reader({ "helper.mts": cyclic }),
    );
    expect(classified[0]?.szs).toBe("Inappropriate");
    expect(classified[0]?.reason).toContain("ImportDeclaration");
  });

  test("default and namespace imports stay opaque even when the module resolves", () => {
    for (const clause of ["helper", "* as helper"]) {
      const src = [
        `import ${clause} from "./helper.mjs";`,
        "/** @ensures{p} forall (x: int ∈ [0, 5)) { call(x) >= 0 } */",
        "export function call(x: number): number {",
        "  return helper(x);",
        "}",
        "",
      ].join("\n");
      const { classified } = emitModule(
        src,
        "main.mts",
        reader({ "helper.mts": HELPER }),
      );
      expect(classified[0]?.szs).toBe("Inappropriate");
    }
  });

  test("a local binding shadows an imported spelling", () => {
    const src = [
      'import { double } from "./helper.mjs";',
      "function double2(x: number): number { return x; }",
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { use(x) >= 0 } */",
      "export function use(x: number): number {",
      "  const double = 1;",
      "  return double2(x);",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(
      src,
      "main.mts",
      reader({ "helper.mts": HELPER }),
    );
    // The local const shadows the import inside the body; the call to
    // double2 is unaffected either way.
    expect(classified.map((c) => c.szs)).toEqual([]);
  });

  test("no reader means the disk, and a missing file degrades rather than throws", () => {
    const { classified } = emitModule(TWICE, "/nonexistent/main.mts");
    expect(classified[0]?.szs).toBe("Inappropriate");
  });
});

describe("class-typed parameters across modules", () => {
  const BOX = [
    "export class Box {",
    "  readonly v: number;",
    "  constructor(v: number) {",
    "    this.v = v;",
    "  }",
    "}",
    "",
  ].join("\n");

  test("an imported class types a parameter under its own module", () => {
    const main = [
      'import { Box } from "./box.mjs";',
      "/** @ensures{reads} forall (x: int ∈ [0, 10)) { unwrap(new Box(x)) === x } */",
      "export function unwrap(b: Box): number {",
      "  return b.v;",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(
      main,
      "main.mts",
      reader({ "box.mts": BOX }),
    );
    expect(classified).toEqual([]);
    const unwrap = emission.declarations.find((d) => d.name === "unwrap")!;
    assert(unwrap.kind === "function");
    expect(unwrap.params).toEqual([
      { name: "b", type: { class: "Box", module: "box.mts" } },
    ]);
    expect(unwrap.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "field-read",
        className: "Box",
        module: "box.mts",
        field: "v",
        object: { kind: "id", name: "b" },
      },
    });
  });

  test("a method call on an imported class carries its module", () => {
    const box = [
      "export class Box {",
      "  readonly v: number;",
      "  constructor(v: number) {",
      "    this.v = v;",
      "  }",
      "  twice(): number {",
      "    return this.v * 2;",
      "  }",
      "}",
      "",
    ].join("\n");
    const main = [
      'import { Box } from "./box.mjs";',
      "/** @ensures{reads} forall (x: int ∈ [0, 10)) { unwrap(new Box(x)) === 2 * x } */",
      "export function unwrap(b: Box): number {",
      "  return b.twice();",
      "}",
      "",
    ].join("\n");
    const { emission, classified } = emitModule(
      main,
      "main.mts",
      reader({ "box.mts": box }),
    );
    expect(classified).toEqual([]);
    const unwrap = emission.declarations.find((d) => d.name === "unwrap")!;
    assert(unwrap.kind === "function");
    expect(unwrap.body[0]).toEqual({
      kind: "return",
      expr: {
        kind: "method-call",
        className: "Box",
        module: "box.mts",
        name: "twice",
        object: { kind: "id", name: "b" },
        args: [],
      },
    });
  });

  test("an instance of a same-named local class is not the imported one", () => {
    const main = [
      'import { Box } from "./box.mjs";',
      "export class Local {",
      "  readonly v: number;",
      "  constructor(v: number) {",
      "    this.v = v;",
      "  }",
      "}",
      "/** @ensures{reads} forall (x: int ∈ [0, 10)) { unwrap(new Local(x)) === x } */",
      "export function unwrap(b: Box): number {",
      "  return b.v;",
      "}",
      "",
    ].join("\n");
    const { classified } = emitModule(
      main,
      "main.mts",
      reader({ "box.mts": BOX }),
    );
    expect(classified[0]!.szs).toBe("Error");
    expect(classified[0]!.reason).toMatch(
      /yields an instance of 'Local', not an instance of 'box.mts::Box'/,
    );
  });
});
