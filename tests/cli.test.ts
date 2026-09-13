import { describe, it, expect } from "vitest";
import { runMain, useTempProject } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";

describe("cli main", () => {
  useTempProject("lakatos-cli-", {
    "baz.ts": `/** @ensures{pos} forall (n: nat) { baz(n) >= 0 } */\nexport function baz(n: number): number { return n; }\n`,
    "shadow.d.ts": `/** @ensures{pos2} forall (n: nat) { baz(n) >= 0 } */\nexport declare function baz(n: number): number;\n`,
  });

  it("skips declaration files matched by a glob", async () => {
    const { code, stdout } = await runMain(["check", "*.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toMatchObject({ file: "baz.ts" });
  });

  it("honors an explicitly named declaration file", async () => {
    const { code, stdout } = await runMain(["check", "shadow.d.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toMatchObject({ property: "pos2" });
  });

  it("honors a glob that targets declaration files", async () => {
    const { code, stdout } = await runMain(["check", "*.d.ts"]);
    expect(code).toBe(1);
    expect(JSON.parse(stdout[0]!).annotations).toHaveLength(1);
  });

  it("returns 2 on unknown command", async () => {
    const { code, stderr } = await runMain(["frobnicate", "baz.ts"]);
    expect(code).toBe(2);
    expect(stderr[0]).toContain("usage: lakatos");
  });

  it("returns 2 with usage on an unknown option", async () => {
    const { code, stderr } = await runMain(["--halp"]);
    expect(code).toBe(2);
    expect(stderr).toHaveLength(1);
    expect(stderr[0]).toContain("usage: lakatos");
  });

  it("prints help on --help and exits 0", async () => {
    const { code, stdout, stderr } = await runMain(["--help"]);
    expect(code).toBe(0);
    expect(stderr).toEqual([]);
    const help = stdout.join("\n");
    expect(help).toContain("usage: lakatos");
    expect(help).toContain("prove");
    expect(help).toContain("refute");
    expect(help).toContain("check");
    expect(help).toContain("--seed");
    expect(help).toContain("--help");
  });

  it("prints the same help on -h", async () => {
    const { code, stdout } = await runMain(["-h"]);
    expect(code).toBe(0);
    expect(stdout).toEqual((await runMain(["--help"])).stdout);
  });

  it("returns 2 on a non-integer --seed", async () => {
    expect((await runMain(["refute", "--seed", "4.2", "baz.ts"])).code).toBe(2);
  });

  it("returns 2 on an out-of-range --seed", async () => {
    expect(
      (await runMain(["refute", "--seed", String(2 ** 32), "baz.ts"])).code,
    ).toBe(2);
  });

  it("returns 2 when no .ts files match the patterns", async () => {
    expect((await runMain(["check", "*.nope"])).code).toBe(2);
  });
});

describe("cli main without a tsconfig", () => {
  useTempProject(
    "lakatos-cli-nodiscover-",
    {
      "baz.ts": `/** @ensures{pos} forall (n: nat) { baz(n) >= 0 } */\nexport function baz(n: number): number { return n; }\n`,
    },
    { tsconfig: false },
  );

  it("returns 2 when no patterns are given and nothing is discoverable", async () => {
    const { code, stderr } = await runMain(["check"]);
    expect(code).toBe(2);
    expect(stderr).toHaveLength(1);
    expect(stderr[0]).toBe(
      'error: no tsconfig.json to discover sources from; pass files or globs (e.g. lakatos refute "src/**/*.ts")',
    );
  });
});

describe("cli input errors", () => {
  useTempProject("lakatos-cli-inputerror-", {
    "mixed.ts": `class Hidden {
  /** @ensures{p} forall (x: int) { Hidden.id(x) === x } */
  static id(x: number): number { return x; }
}

/** @ensures{q} forall (x: int ∈ [0, 5)) { ok(x) === x } */
export function ok(x: number): number { return x; }
`,
    "dup.ts": `/**
 * @ensures{d} forall (x: int) { f(x) === x }
 * @ensures{d} forall (x: int) { f(x) === x }
 */
export function f(x: number): number { return x; }
`,
  });

  it("check stub reports InputError entries beside NotTried and exits 2", async () => {
    const { code, stdout, stderr } = await runMain(["check", "mixed.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toContainEqual({
      file: "mixed.ts",
      function: "Hidden.id",
      property: "p",
      szs: "InputError",
      error: expect.stringMatching(/^mixed\.ts:2: .*not exported/),
    });
    expect(env.annotations).toContainEqual({
      file: "mixed.ts",
      function: "ok",
      property: "q",
      szs: "NotTried",
    });
    expect(stderr.join("\n")).toContain("mixed.ts:2: ");
    expect(stderr.join("\n")).toContain("not exported");
  });

  it("refute with only input errors keeps the contract and exits 2", async () => {
    const { code, stdout, stderr } = await runMain(["refute", "dup.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toEqual({
      file: "dup.ts",
      function: "f",
      property: "d",
      szs: "InputError",
      error: expect.stringMatching(/^dup\.ts:2: duplicate property name 'd'/),
    });
    expect(stderr.join("\n")).toContain(
      "dup.ts:2: duplicate property name 'd'",
    );
  });
});

// User-facing compile errors (malformed formulas, unsupported constructs,
// bad references) must exit 2 with a one-line diagnostic, not escape main()
// as an uncaught exception. One case per LemmaError-throwing module keeps
// the whole compile front-end pinned to the contract: reverting any module's
// throws to plain Error fails its case here. These use `lakatos refute` —
// compilation fails before vitest is spawned, so no timeout is needed.
//
// `wrapped` marks errors thrown per-annotation inside buildSpec, which the
// build-spec seam prefixes with `file:line: @ensures{name}:`. Extract-phase
// input errors (duplicate names, ineligible/unexported/unnameable subjects)
// no longer throw at all — they surface as per-annotation InputError
// entries (see "cli input errors").
interface CompileErrorCase {
  name: string;
  file: string;
  source: string;
  wrapped: boolean;
  property: string;
  /** True when lemma's own parsers throw the error — the rejects both
   * engines must refuse identically. False marks refute-only resolution
   * checks (unexported references, unresolvable domains). */
  parseLevel: boolean;
  expected: string[];
}

const COMPILE_ERROR_CASES: CompileErrorCase[] = [
  {
    name: "a malformed quantifier prefix (prefix-parser)",
    file: "malformed.ts",
    source: `/** @ensures{shapely} for every (n: nat), malformed(n) >= 0 */\nexport function malformed(n: number): number { return n; }\n`,
    wrapped: true,
    property: "shapely",
    parseLevel: true,
    expected: ["expected 'forall'"],
  },
  {
    name: "a leading existential quantifier (prefix-parser)",
    file: "existential.ts",
    source: `/** @ensures{someone} exists (n: nat), ex(n) > 0 */\nexport function ex(n: number): number { return n; }\n`,
    wrapped: true,
    property: "someone",
    parseLevel: true,
    expected: ["existential quantifiers"],
  },
  {
    name: "an unresolvable domain (class-domain resolution)",
    file: "baddomain.ts",
    source: `/** @ensures{rounds} forall (x: float) { rounder(x) >= 0 } */\nexport function rounder(x: number): number { return x; }\n`,
    wrapped: true,
    property: "rounds",
    parseLevel: false,
    expected: [
      "domain 'float' is neither a primitive domain",
      "nor an exported class declared in",
    ],
  },
  {
    name: "an existential inside the body (formula-lexer)",
    file: "bodyexists.ts",
    source: `/** @ensures{someInBody} forall (n: nat) { inBody(n) > 0 ∧ exists m, inBody(m) === 0 } */\nexport function inBody(n: number): number { return n; }\n`,
    wrapped: true,
    property: "someInBody",
    parseLevel: true,
    expected: ["existential quantifiers"],
  },
  {
    name: "a nested forall inside the body (formula-lexer)",
    file: "nestedforall.ts",
    source: `/** @ensures{deep} forall (n: nat) { forall (m: nat) { nested(n) >= 0 } } */\nexport function nested(n: number): number { return n; }\n`,
    wrapped: true,
    property: "deep",
    parseLevel: true,
    expected: ["nested quantifiers"],
  },
  {
    name: "JS && at the property's top level (formula-parser)",
    file: "jsconj.ts",
    source: `/** @ensures{conj} forall (n: nat) { jsconj(n) >= 0 && jsconj(n) >= 0 } */\nexport function jsconj(n: number): number { return n; }\n`,
    wrapped: true,
    property: "conj",
    parseLevel: true,
    expected: ["use ∧ for conjunction"],
  },
  {
    name: "a comma-separated binder group (prefix-parser)",
    file: "commagroup.ts",
    source: `/** @ensures{p} forall (a: number, b: number) { 0 <= commagroup(a) } */\nexport function commagroup(a: number, b: number): number { return a; }\n`,
    wrapped: true,
    property: "p",
    parseLevel: true,
    expected: ["invalid domain 'number, b: number'"],
  },
];

describe("cli compile errors (exit-code contract)", () => {
  useTempProject(
    "lakatos-cli-err-",
    Object.fromEntries(COMPILE_ERROR_CASES.map((c) => [c.file, c.source])),
  );

  it.each(COMPILE_ERROR_CASES)(
    "refute on $name exits 2 with a one-line diagnostic",
    async (c) => {
      const { code, stderr } = await runMain(["refute", c.file]);
      expect(code).toBe(2);
      const diagnostics = stderr;
      expect(diagnostics).toHaveLength(1);
      expect(diagnostics[0]).not.toContain("\n");
      if (c.wrapped) {
        expect(diagnostics[0]).toContain(
          `${c.file}:1: @ensures{${c.property}}:`,
        );
      }
      for (const fragment of c.expected) {
        expect(diagnostics[0]).toContain(fragment);
      }
    },
  );

  const PARSE_LEVEL_CASES = COMPILE_ERROR_CASES.filter((c) => c.parseLevel);

  it.each(PARSE_LEVEL_CASES)(
    "prove on $name exits 2 with the same diagnostic as refute",
    async (c) => {
      const refute = await runMain(["refute", c.file]);
      const prove = await runMain(["prove", c.file]);
      expect(prove.code).toBe(2);
      expect(prove.stdout).toEqual(refute.stdout);
      expect(prove.stderr).toEqual(refute.stderr);
    },
  );
});
