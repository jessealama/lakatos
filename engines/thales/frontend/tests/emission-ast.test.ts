import { describe, expect, test } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { schemaValidator } from "../../../../tests/helpers/schema-validator.js";
import { type EmitDecl, emitModule } from "../src/emission.js";
import {
  bridgeModule,
  closureProgram,
  declaredNames,
  referencedNames,
} from "../src/emission-ast.js";
import { type ModuleReader } from "../src/module-graph.js";
import {
  parseScript,
  type Program,
  type Statement,
} from "../../../../tarski/frontend/src/estree.js";
import { stripTypes } from "../../../../tarski/frontend/src/strip-types.js";

const expectValidProgram = schemaValidator(
  new URL("../../../../schemas/tarski-estree.schema.json", import.meta.url),
  "a declaration's ast",
);

/** An in-memory module tree, keyed the way the walk resolves: absolute
 * paths against the importing file's directory. */
function reader(files: Record<string, string>): ModuleReader {
  const abs = new Map(
    Object.entries(files).map(([f, text]) => [path.resolve(f), text]),
  );
  return (file) => abs.get(file);
}

/** The bridge's own document for a module's text. Every expectation in
 * this file is computed this way rather than spelled as node literals: the
 * claim is that a declaration carries a *selection* of the bridge's
 * statements, which a hand-written tree could not witness. */
function bridged(text: string, file: string): Program {
  return parseScript(stripTypes(text, file), file);
}

/** The top-level names a bridged statement binds, spelled here rather than
 * imported, so an expectation does not lean on the code under test. */
function boundNames(stmt: Statement): string[] {
  if (stmt.type === "FunctionDeclaration" || stmt.type === "ClassDeclaration")
    return [stmt.id.name];
  if (stmt.type === "VariableDeclaration")
    // The corpus's declarations all bind one name, so a declarator whose
    // `id` is a pattern binds nothing the expectations below name.
    return stmt.declarations.flatMap((d) =>
      d.id.type === "Identifier" ? [d.id.name] : [],
    );
  return [];
}

/** A module's statements declaring any of `names`, in source order. */
function picked(
  text: string,
  file: string,
  names: readonly string[],
): Statement[] {
  return bridged(text, file).body.filter((s) =>
    boundNames(s).some((n) => names.includes(n)),
  );
}

/** The script a closure must be: the entry's `"use strict"` directive and
 * the statements, in the order given. */
function script(directiveFrom: Program, body: Statement[]): Program {
  return {
    type: "Program",
    sourceType: "script",
    body: [directiveFrom.body[0]!, ...body],
  };
}

/** A declaration by name, narrowed out of the union. */
function decl(declarations: readonly EmitDecl[], name: string): EmitDecl {
  const found = declarations.find(
    (d) => d.kind !== "residual" && d.name === name,
  );
  if (found === undefined) throw new Error(`no declaration named '${name}'`);
  return found;
}

/** The `ast` a declaration carries, or undefined. */
function astOf(declarations: readonly EmitDecl[], name: string) {
  const d = decl(declarations, name);
  return d.kind === "residual" ? undefined : d.ast;
}

const FIXTURE = "engines/thales/tests/fixtures/tracer.ts";
const TRACER = fs.readFileSync(FIXTURE, "utf8");

const CLASSES = "engines/thales/tests/fixtures/classes.ts";
const CLASSES_TEXT = fs.readFileSync(CLASSES, "utf8");

const MODULE_CONSTS = "engines/thales/tests/fixtures/module-consts.ts";
const MODULE_CONSTS_TEXT = fs.readFileSync(MODULE_CONSTS, "utf8");

describe("a declaration's own closure", () => {
  test("a function that reaches nothing carries the directive and itself", () => {
    const { emission } = emitModule(TRACER, FIXTURE);
    const doc = bridged(TRACER, FIXTURE);
    expect(astOf(emission.declarations, "add")).toEqual(
      script(doc, picked(TRACER, FIXTURE, ["add"])),
    );
    expectValidProgram(astOf(emission.declarations, "add"));
  });

  test("a class carries its own declaration, and its members share it", () => {
    const { emission } = emitModule(CLASSES_TEXT, CLASSES);
    const doc = bridged(CLASSES_TEXT, CLASSES);
    for (const name of ["Box", "Gate", "Doubler"]) {
      expect(astOf(emission.declarations, name)).toEqual(
        script(doc, picked(CLASSES_TEXT, CLASSES, [name])),
      );
      expectValidProgram(astOf(emission.declarations, name));
    }
  });
});

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

describe("a closure across modules", () => {
  test("a callee's declaration comes first, from the module that has it", () => {
    const { emission } = emitModule(
      TWICE,
      "main.mts",
      reader({ "helper.mts": HELPER }),
    );
    const helperFile = path.resolve("helper.mts");
    expect(astOf(emission.declarations, "twice")).toEqual(
      script(bridged(TWICE, "main.mts"), [
        ...picked(HELPER, helperFile, ["double"]),
        ...picked(TWICE, "main.mts", ["twice"]),
      ]),
    );
    // The dependency's own declaration reaches nothing of the entry's.
    expect(astOf(emission.declarations, "double")).toEqual(
      script(
        bridged(HELPER, helperFile),
        picked(HELPER, helperFile, ["double"]),
      ),
    );
  });

  test("a class the closure names is pulled in, in source order", () => {
    const src = [
      "export class Other {",
      "  #v: number;",
      "  constructor(v: number) {",
      "    this.#v = v;",
      "  }",
      "  get v(): number {",
      "    return this.#v;",
      "  }",
      "}",
      "export class Holder {",
      "  #n: number;",
      "  constructor(n: number) {",
      "    this.#n = n;",
      "  }",
      "  /** @ensures{p} forall (n: number) { Object.is(new Holder(n).made(), 1) } */",
      "  made(): number {",
      "    return new Other(1).v;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "holder.ts");
    expect(astOf(emission.declarations, "Holder")).toEqual(
      script(
        bridged(src, "holder.ts"),
        picked(src, "holder.ts", ["Other", "Holder"]),
      ),
    );
  });
});

describe("a closure over module constants", () => {
  test("the constants a function reads come with it, in source order", () => {
    const { emission } = emitModule(MODULE_CONSTS_TEXT, MODULE_CONSTS);
    expect(astOf(emission.declarations, "hoursToMilliseconds")).toEqual(
      script(
        bridged(MODULE_CONSTS_TEXT, MODULE_CONSTS),
        picked(MODULE_CONSTS_TEXT, MODULE_CONSTS, [
          "millisecondsInSecond",
          "millisecondsInMinute",
          "millisecondsInHour",
          "hoursToMilliseconds",
        ]),
      ),
    );
  });

  test("a constant the IR erases is still in the closure", () => {
    // `magnitude`'s IR is a `builtin` node: nothing in it says the body
    // reaches `safeMathAbs`. A closure read off the IR would assemble a
    // script that `ReferenceError`s, which is why it is read off the
    // bridge's identifiers instead.
    const { emission } = emitModule(MODULE_CONSTS_TEXT, MODULE_CONSTS);
    expect(astOf(emission.declarations, "magnitude")).toEqual(
      script(
        bridged(MODULE_CONSTS_TEXT, MODULE_CONSTS),
        picked(MODULE_CONSTS_TEXT, MODULE_CONSTS, ["safeMathAbs", "magnitude"]),
      ),
    );
  });

  test("a function reaching one constant carries exactly that one", () => {
    const { emission } = emitModule(MODULE_CONSTS_TEXT, MODULE_CONSTS);
    expect(astOf(emission.declarations, "secondsToMilliseconds")).toEqual(
      script(
        bridged(MODULE_CONSTS_TEXT, MODULE_CONSTS),
        picked(MODULE_CONSTS_TEXT, MODULE_CONSTS, [
          "millisecondsInSecond",
          "secondsToMilliseconds",
        ]),
      ),
    );
  });
});

describe("closures that do not close", () => {
  test("a renamed import leaves the importer without an ast", () => {
    const main = [
      'import { double as dbl } from "./helper.mjs";',
      "/** @ensures{p} forall (x: int ∈ [0, 20)) { twice(x) === 4 * x } */",
      "export function twice(x: number): number {",
      "  return dbl(x) + dbl(x);",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(
      main,
      "main.mts",
      reader({ "helper.mts": HELPER }),
    );
    // Authoring `const dbl = double;` is exactly what the issue forbids,
    // so the importer carries nothing — and the dependency still does.
    expect(astOf(emission.declarations, "twice")).toBeUndefined();
    expect(astOf(emission.declarations, "double")).toBeDefined();
  });

  test("one name declared by two modules of a closure leaves no ast", () => {
    const dep = [
      "function helper(x: number): number {",
      "  return x + 1;",
      "}",
      "export function step(x: number): number {",
      "  return helper(x);",
      "}",
      "",
    ].join("\n");
    const main = (local: string) =>
      [
        'import { step } from "./dep.mjs";',
        `function ${local}(x: number): number {`,
        "  return x * 2;",
        "}",
        "/** @ensures{p} forall (x: int ∈ [0, 5)) { top(x) >= 0 } */",
        "export function top(x: number): number {",
        `  return step(x) + ${local}(x);`,
        "}",
        "",
      ].join("\n");
    // The entry's own helper is spelled apart from the dependency's: one
    // script, two names, one statement each.
    expect(
      astOf(
        emitModule(main("scale"), "main.mts", reader({ "dep.mts": dep }))
          .emission.declarations,
        "top",
      ),
    ).toBeDefined();
    // Spelled the same, the closure would need two statements called
    // `helper` in one script. Nothing renames either, so there is no
    // script.
    expect(
      astOf(
        emitModule(main("helper"), "main.mts", reader({ "dep.mts": dep }))
          .emission.declarations,
        "top",
      ),
    ).toBeUndefined();
  });
});

describe("what the frontend does not refuse", () => {
  test("an async callee is carried as the bridge left it", () => {
    // The frontend selects statements; Lean owns every refusal verdict, so
    // the `async` declaration travels and the decoder is what refuses it.
    const src = [
      "export async function slow(x: number): Promise<number> {",
      "  return x;",
      "}",
      "/** @ensures{p} forall (x: int ∈ [0, 5)) { wrap(x) >= 0 } */",
      "export function wrap(x: number): number {",
      "  return slow.length + x;",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "async.ts");
    const carried = picked(src, "async.ts", ["slow", "wrap"]);
    expect(carried[0]).toMatchObject({
      type: "FunctionDeclaration",
      async: true,
    });
    expect(astOf(emission.declarations, "wrap")).toEqual(
      script(bridged(src, "async.ts"), carried),
    );
  });
});

describe("what a reference is", () => {
  test("a non-computed member name is not a reference; a computed one is", () => {
    const src = [
      "const lo = 1;",
      "export class Holder {",
      "  #lo: number;",
      "  constructor(v: number) {",
      "    this.#lo = v;",
      "  }",
      "  /** @ensures{p} forall (v: number) { Object.is(new Holder(v).plain(), v) } */",
      "  plain(): number {",
      "    return this.#lo;",
      "  }",
      "}",
      "",
    ].join("\n");
    const { emission } = emitModule(src, "plain.ts");
    expect(astOf(emission.declarations, "Holder")).toEqual(
      script(bridged(src, "plain.ts"), picked(src, "plain.ts", ["Holder"])),
    );

    const computed = src.replace("return this.#lo;", "return this.#lo + lo;");
    const { emission: withRead } = emitModule(computed, "plain.ts");
    expect(astOf(withRead.declarations, "Holder")).toEqual(
      script(
        bridged(computed, "plain.ts"),
        picked(computed, "plain.ts", ["lo", "Holder"]),
      ),
    );
  });
});

/** Every `.ts` the emission store is built from. An empty allowlist makes
 * any future exception visible, which is acceptance criterion 1's frontend
 * half: every emitted declaration carries an ast. */
function storeInputs(): string[] {
  const roots = [
    "engines/thales/tests/fixtures",
    "engines/thales/tests/conformance",
  ];
  const out: string[] = [];
  const walk = (dir: string): void => {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(full);
      // A declaration file is never an entry: it has no runtime statements
      // at all, which is why `tsc` declines to transpile one.
      else if (entry.name.endsWith(".ts") && !entry.name.endsWith(".d.ts"))
        out.push(full);
    }
  };
  for (const root of roots) walk(root);
  return out.sort();
}

describe("every emitted declaration carries its AST", () => {
  test.each(storeInputs())("%s", (file) => {
    const { emission } = emitModule(fs.readFileSync(file, "utf8"), file);
    const without = emission.declarations
      .filter((d) => d.kind !== "residual" && d.ast === undefined)
      .map((d) => (d.kind === "residual" ? "" : d.name));
    expect(without).toEqual([]);
  });
});

describe("the pieces a closure is built from", () => {
  test("a module with no script to bridge answers undefined", () => {
    // `transpileModule` on a declaration file fails outright rather than
    // answering empty text. Containment is the emitter's rule, so this
    // degrades one field instead of ending the run.
    expect(
      bridgeModule('declare module "@example/units" {\n}\n', "units.d.ts"),
    ).toBeUndefined();
    const { emission } = emitModule(
      'declare module "@example/units" {\n  export function scale(x: number): number;\n}\n',
      "units.d.ts",
    );
    expect(emission.declarations).toEqual([]);
  });

  test("a statement that binds no top-level name declares nothing", () => {
    const doc = bridged("const k = 1;\nk;\nclass C {}\n", "names.ts");
    expect(doc.body.map(declaredNames)).toEqual([[], ["k"], [], ["C"]]);
  });

  test("a non-computed member name and a key are not references", () => {
    // `o.e`, the key `a`, the field name `g`, and the method name `m` are
    // names in their own right, not references. `o[f]` is a reference, and
    // so are the values. An object literal's computed key `[c]` is an
    // expression, so `c` is a reference too. A *class* computed key is an
    // `Unsupported` placeholder the bridge kept no name inside, so `i` and
    // `j` are not here — and a closure carrying one is a closure the
    // decoder refuses, so it never replays. `C` and `o` are their own
    // declarations' ids, which the over-approximation collects and the
    // lookup then resolves to themselves.
    const doc = bridged(
      [
        "const o = { a: b, [c]: d };",
        "o.e;",
        "o[f];",
        "class C { g = h; [i] = j; m() {} }",
        "",
      ].join("\n"),
      "refs.ts",
    );
    expect([...referencedNames(doc.body)].sort()).toEqual([
      "C",
      "b",
      "c",
      "d",
      "f",
      "h",
      "o",
    ]);
  });

  test("a closure whose home or reach was not bridged has no script", () => {
    const text =
      'import { g } from "./g.mjs";\nexport function f() {\n  return g();\n}\n';
    const program = bridgeModule(text, "main.mts")!;
    const names = new Map([
      ["f", { module: "", name: "f" }],
      ["g", { module: "g.mts", name: "g" }],
    ]);
    // The declaration's own module is not among the walked ones.
    expect(closureProgram({ module: "", name: "f" }, [])).toBeUndefined();
    // Its module is, but the module it reaches into is not: the bridge
    // could not read that one, so there is no closed script.
    expect(
      closureProgram({ module: "", name: "f" }, [
        { qualifier: "", program, names },
      ]),
    ).toBeUndefined();
  });
});
