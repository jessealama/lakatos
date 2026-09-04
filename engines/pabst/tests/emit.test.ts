import { describe, it, expect } from "vitest";
import { emit } from "../src/emit.js";
import type { PropertySpec } from "../src/ir.js";

const spec: PropertySpec = {
  name: "nonzero",
  functionName: "foo",
  binders: [
    { varName: "x", domain: "int" },
    { varName: "y", domain: "number" },
  ],
  body: "foo(x, y) !== 0",
  preconditions: ["Number.isInteger(y)"],
  freeExports: ["foo"],
  location: { file: "foo.ts", line: 1 },
};

describe("emit", () => {
  const out = emit([spec], "foo.ts", "out/foo.pabst.test.ts", 42);

  it("imports vitest + @fast-check/vitest and the module", () => {
    expect(out).toContain('import { describe } from "vitest";');
    expect(out).toContain('import { test, fc } from "@fast-check/vitest";');
    expect(out).toContain('import * as __M from "../foo";');
    expect(out).toContain("const { foo } = __M;");
  });

  it("emits the describe hierarchy and test.prop with arbitraries", () => {
    expect(out).toContain('describe("pabst", () => {');
    expect(out).toContain('describe("foo", () => {');
    expect(out).toContain(
      'test.prop([fc.integer(), fc.double()], { seed: 42, reporter: (d) => __pabstReport("foo.ts", "foo", "nonzero", ["x", "y"], d) })("nonzero", (x, y) => {',
    );
  });

  it("lifts preconditions and returns the body without a redundant typeof guard", () => {
    expect(out).toContain("fc.pre(Number.isInteger(y));");
    expect(out).toContain("const __r = (foo(x, y) !== 0);");
    expect(out).not.toContain('typeof __r !== "boolean"');
    expect(out).toContain("return __r;");
  });

  it("passes a reporter that names the property and binds the counterexample", () => {
    expect(out).toContain(
      'test.prop([fc.integer(), fc.double()], { seed: 42, reporter: (d) => __pabstReport("foo.ts", "foo", "nonzero", ["x", "y"], d) })("nonzero", (x, y) => {',
    );
  });

  it("imports the reporter from the runtime library once", () => {
    // "lakatos" is the root package name (the self-reference the
    // generated tests resolve), distinct from any bin name.
    expect(out).toContain(
      'import { report as __pabstReport, bool as __bool, budget as __pabstBudget } from "lakatos/runtime";',
    );
    // no inline copy of the helper
    expect(out).not.toContain("function __pabstReport(");
    // a single import, no matter how many properties
    const multi = emit(
      [spec, { ...spec, name: "other" }],
      "foo.ts",
      "out/foo.pabst.test.ts",
      42,
    );
    const occurrences = multi.split('from "lakatos/runtime"').length - 1;
    expect(occurrences).toBe(1);
  });
});

const instanceSpec: PropertySpec = {
  name: "incAddsOne",
  functionName: "inc",
  className: "Counter",
  isStatic: false,
  binders: [{ varName: "x", domain: "int" }],
  body: "new Counter(x).inc().value === x + 1",
  preconditions: [],
  freeExports: ["Counter"],
  location: { file: "counter.ts", line: 1 },
};

const staticSpec: PropertySpec = {
  name: "matchesSubtraction",
  functionName: "negate",
  className: "Arith",
  isStatic: true,
  binders: [{ varName: "x", domain: "number" }],
  body: "Object.is(Arith.negate(x), 0 - x)",
  preconditions: [],
  freeExports: ["Arith"],
  location: { file: "arith.ts", line: 1 },
};

describe("emit — import path and exports", () => {
  it("prefixes a non-relative import specifier with ./", () => {
    // Source sits below the output dir, so path.relative yields a bare
    // 'sub/bar' that must be made explicitly relative.
    const out = emit(
      [{ ...spec, freeExports: [] }],
      "sub/bar.ts",
      "out.pabst.test.ts",
      42,
    );
    expect(out).toContain('import * as __M from "./sub/bar";');
  });

  it("omits the destructuring line when there are no free exports", () => {
    const out = emit(
      [{ ...spec, freeExports: [] }],
      "foo.ts",
      "out/foo.pabst.test.ts",
      42,
    );
    expect(out).not.toContain("} = __M;");
  });
});

describe("emit — class methods", () => {
  it("nests describe(class) > describe(method) for an instance method", () => {
    const out = emit(
      [instanceSpec],
      "counter.ts",
      "out/counter.pabst.test.ts",
      7,
    );
    expect(out).toContain('describe("Counter", () => {');
    expect(out).toContain('describe("inc", () => {');
  });

  it("passes the # qualified name to the reporter for an instance method", () => {
    const out = emit(
      [instanceSpec],
      "counter.ts",
      "out/counter.pabst.test.ts",
      7,
    );
    expect(out).toContain(
      '__pabstReport("counter.ts", "Counter#inc", "incAddsOne", ["x"], d)',
    );
  });

  it("passes the . qualified name to the reporter for a static method", () => {
    const out = emit([staticSpec], "arith.ts", "out/arith.pabst.test.ts", 7);
    expect(out).toContain('describe("Arith", () => {');
    expect(out).toContain('describe("negate", () => {');
    expect(out).toContain(
      '__pabstReport("arith.ts", "Arith.negate", "matchesSubtraction", ["x"], d)',
    );
  });
});

describe("emit — bounded intervals", () => {
  it("passes range constraints through to the arbitraries", () => {
    const bounded: PropertySpec = {
      ...spec,
      binders: [
        { varName: "x", domain: "int", range: { min: "1", max: "30" } },
        { varName: "y", domain: "number", range: { min: "0", max: "1" } },
      ],
    };
    const out = emit([bounded], "foo.ts", "out/foo.pabst.test.ts", 42);
    expect(out).toContain(
      "test.prop([fc.integer({ min: 1, max: 30 }), fc.double({ min: 0, max: 1, noNaN: true })]",
    );
  });

  it("leaves unranged binders exactly as before", () => {
    const out = emit([spec], "foo.ts", "out/foo.pabst.test.ts", 42);
    expect(out).toContain("test.prop([fc.integer(), fc.double()]");
  });
});

const pointDomain = {
  className: "Point",
  ctorParams: [
    { name: "x", domain: "number" as const },
    { name: "y", domain: "number" as const },
  ],
};

const classSpec: PropertySpec = {
  name: "nonNegative",
  functionName: "distance",
  className: "Point",
  binders: [
    { varName: "p", domain: pointDomain },
    { varName: "q", domain: pointDomain },
  ],
  body: '__bool(0 <= p.distance(q), "0 <= p.distance(q)")',
  preconditions: [],
  freeExports: ["Point"],
  location: { file: "point.ts", line: 1 },
};

describe("emit — class binders", () => {
  const out = emit([classSpec], "point.ts", "out/point.pabst.test.ts", 42);

  it("draws each class binder as its constructor-argument tuple", () => {
    expect(out).toContain(
      "test.prop([fc.tuple(fc.double(), fc.double()), fc.tuple(fc.double(), fc.double())]",
    );
    expect(out).toContain("(__args_p, __args_q) => {");
  });

  it("constructs each instance and discards tuples the constructor rejects", () => {
    expect(out).toContain("let p!: Point;");
    expect(out).toContain(
      "try { p = new Point(...__args_p); } catch { fc.pre(false); }",
    );
    expect(out).toContain("let q!: Point;");
    expect(out).toContain(
      "try { q = new Point(...__args_q); } catch { fc.pre(false); }",
    );
  });

  it("tells the reporter which binders are constructions", () => {
    const shape = '{"className":"Point","params":[null,null]}';
    expect(out).toContain(`["p", "q"], d, [${shape}, ${shape}])`);
  });

  it("imports the binder class from the module under test", () => {
    expect(out).toContain("const { Point } = __M;");
  });

  it("passes no constructor list when every binder is primitive", () => {
    const plain = emit([spec], "foo.ts", "out/foo.pabst.test.ts", 42);
    expect(plain).not.toContain("], d, [");
  });
});

const boxDomain = {
  className: "Box",
  ctorParams: [
    { name: "p", domain: pointDomain },
    { name: "k", domain: "number" as const },
  ],
};

const nestedSpec: PropertySpec = {
  name: "wide",
  functionName: "width",
  className: "Box",
  binders: [{ varName: "b", domain: boxDomain }],
  body: '__bool(0 <= b.width(), "0 <= b.width()")',
  preconditions: [],
  freeExports: ["Box", "Point"],
  location: { file: "box.ts", line: 1 },
};

describe("emit — nested class binders", () => {
  const out = emit([nestedSpec], "box.ts", "out/box.pabst.test.ts", 42);

  it("draws the nested tuple", () => {
    expect(out).toContain(
      "test.prop([fc.tuple(fc.tuple(fc.double(), fc.double()), fc.double())]",
    );
  });

  it("constructs innermost-out inside one try, so any throw discards", () => {
    expect(out).toContain("let b!: Box;");
    expect(out).toContain(
      "try { b = new Box(new Point(...__args_b[0]), __args_b[1]); } " +
        "catch { fc.pre(false); }",
    );
  });

  it("tells the reporter the whole construction tree", () => {
    expect(out).toContain(
      '["b"], d, [{"className":"Box","params":' +
        '[{"className":"Point","params":[null,null]},null]}])',
    );
  });
});

const enumeratedSpec: PropertySpec = {
  name: "pos",
  functionName: "square",
  binders: [
    { varName: "n", domain: "int", range: { min: "1", max: "10" } },
    { varName: "b", domain: "boolean" },
  ],
  body: '__bool(square(n) > 0, "square(n) > 0")',
  preconditions: ['__bool(b, "b")'],
  freeExports: ["square"],
  cases: 20,
  location: { file: "small.ts", line: 1 },
};

describe("emit — enumerated specs", () => {
  const out = emit([enumeratedSpec], "small.ts", "out/small.pabst.test.ts", 42);

  it("imports the budget reporter beside the others", () => {
    expect(out).toContain(
      'import { report as __pabstReport, bool as __bool, budget as __pabstBudget } from "lakatos/runtime";',
    );
  });

  it("emits a plain test with an explicit timeout above the loop budget", () => {
    expect(out).toContain('    test("pos", { timeout: 8000 }, () => {');
    expect(out).not.toContain("test.prop(");
  });

  it("nests one ascending loop per binder, in binder order", () => {
    expect(out).toContain(
      "      for (let n = 1; n <= 10; n++) {\n        for (const b of [false, true]) {",
    );
  });

  it("checks the wall clock before every tuple and reports the budget with the count", () => {
    expect(out).toContain(
      '          if (performance.now() - __t0 > 4000) __pabstBudget("small.ts", "square", "pos", __done, 20);',
    );
    expect(out).toContain("          __done++;");
  });

  it("skips a tuple a precondition rejects, inside the try", () => {
    expect(out).toContain('            if (!(__bool(b, "b"))) continue;');
  });

  it("reports the first failing tuple through the runtime reporter", () => {
    expect(out).toContain(
      '      const __fail = (__cx: unknown[], __e: { message?: string } | null) => __pabstReport("small.ts", "square", "pos", ["n", "b"], { failed: true, counterexample: __cx, errorInstance: __e });',
    );
    expect(out).toContain(
      "            __fail([n, b], __e instanceof Error ? __e : { message: String(__e) });",
    );
    expect(out).toContain("          if (!__r) __fail([n, b], null);");
  });

  it("leaves a sampled spec on test.prop", () => {
    const both = emit(
      [spec, enumeratedSpec],
      "small.ts",
      "out/small.pabst.test.ts",
      42,
    );
    expect(both).toContain("test.prop([fc.integer(), fc.double()]");
    expect(both).toContain('test("pos", { timeout: 8000 }');
  });
});
