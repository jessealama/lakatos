import { describe, it, expect, afterAll, beforeAll, beforeEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import {
  announcedRunDir,
  runMain,
  useTempProject,
  withoutSkipWarning,
} from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { RUN_ROOT } from "../src/run-dir.js";

const repoRoot = process.cwd();

describe("cli main", () => {
  useTempProject("lakatos-cli-", {
    "baz.ts": `/** @ensures{pos} forall (n: nat) { baz(n) >= 0 } */\nexport function baz(n: number): number { return n; }\n`,
    "shadow.d.ts": `/** @ensures{pos2} forall (n: nat) { baz(n) >= 0 } */\nexport declare function baz(n: number): number;\n`,
  });

  it("skips declaration files matched by a glob", () => {
    const { code, stdout } = runMain(["check", "*.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toMatchObject({ file: "baz.ts" });
  });

  it("honors an explicitly named declaration file", () => {
    const { code, stdout } = runMain(["check", "shadow.d.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toMatchObject({ property: "pos2" });
  });

  it("honors a glob that targets declaration files", () => {
    const { code, stdout } = runMain(["check", "*.d.ts"]);
    expect(code).toBe(1);
    expect(JSON.parse(stdout[0]!).annotations).toHaveLength(1);
  });

  it("returns 2 on unknown command", () => {
    const { code, stderr } = runMain(["frobnicate", "baz.ts"]);
    expect(code).toBe(2);
    expect(stderr[0]).toContain("usage: lakatos");
  });

  it("returns 2 when no patterns are given and nothing is discoverable", () => {
    const { code, stderr } = runMain(["check"]);
    expect(code).toBe(2);
    expect(stderr).toHaveLength(1);
    expect(stderr[0]).toBe(
      'error: cannot determine where your source code is; pass files or globs (e.g. lakatos refute "src/**/*.ts")',
    );
  });

  it("returns 2 with usage on an unknown option", () => {
    const { code, stderr } = runMain(["--halp"]);
    expect(code).toBe(2);
    expect(stderr).toHaveLength(1);
    expect(stderr[0]).toContain("usage: lakatos");
  });

  it("prints help on --help and exits 0", () => {
    const { code, stdout, stderr } = runMain(["--help"]);
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

  it("prints the same help on -h", () => {
    const { code, stdout } = runMain(["-h"]);
    expect(code).toBe(0);
    expect(stdout).toEqual(runMain(["--help"]).stdout);
  });

  it("returns 2 on a non-integer --seed", () => {
    expect(runMain(["refute", "--seed", "4.2", "baz.ts"]).code).toBe(2);
  });

  it("returns 2 on an out-of-range --seed", () => {
    expect(runMain(["refute", "--seed", String(2 ** 32), "baz.ts"]).code).toBe(
      2,
    );
  });

  it("returns 2 when no .ts files match the patterns", () => {
    expect(runMain(["check", "*.nope"]).code).toBe(2);
  });
});

describe("check stub", () => {
  useTempProject("lakatos-cli-stub-", {
    "annotated.ts": `/** @ensures{pos} forall (n: nat) { annotated(n) >= 0 } */\nexport function annotated(n: number): number { return n; }\n`,
    "unexported.ts": `/** @ensures{agrees} forall (n: nat) { unexported(n) === helper(n) } */\nexport function unexported(n: number): number { return n; }\nfunction helper(n: number): number { return n; }\n`,
    "malformed.ts": `/** @ensures{shapely} for every (n: nat), malformed(n) >= 0 */\nexport function malformed(n: number): number { return n; }\n`,
  });

  it("lists every annotation as NotTried and exits 1", () => {
    const { code, stdout, stderr } = runMain(["check", "annotated.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toHaveLength(1);
    expect(env.annotations[0]).toEqual({
      file: "annotated.ts",
      function: "annotated",
      property: "pos",
      szs: "NotTried",
    });
    expect(env.seed).toBeUndefined();
    expect(env.generated).toBeUndefined();
    expect(env.passed).toBeUndefined();
    expect(env.failed).toBeUndefined();
    expect(stderr.join("\n")).toContain("check is not implemented yet");
  });

  // The stub enumerates through lemma, so only lemma can condemn a formula.
  // A reference the refuter cannot lower is not a verdict on the annotation:
  // the prover has no such restriction, and check answers for both.
  it("reports an annotation only the refuter rejects as NotTried", () => {
    const { code, stdout } = runMain(["check", "unexported.ts"]);
    expect(code).toBe(1);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "unexported.ts",
        function: "unexported",
        property: "agrees",
        szs: "NotTried",
      },
    ]);
  });

  it("still exits 2 on a formula lemma itself cannot parse", () => {
    const { code, stderr } = runMain(["check", "malformed.ts"]);
    expect(code).toBe(2);
    const diagnostics = withoutSkipWarning(stderr);
    expect(diagnostics).toHaveLength(1);
    expect(diagnostics[0]).toContain("malformed.ts:1: @ensures{shapely}:");
    expect(diagnostics[0]).toContain("expected 'forall'");
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

  it("check stub reports InputError entries beside NotTried and exits 2", () => {
    const { code, stdout, stderr } = runMain(["check", "mixed.ts"]);
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

  it("refute with only input errors keeps the contract and exits 2", () => {
    const { code, stdout, stderr } = runMain(["refute", "dup.ts"]);
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

describe("cli zero-argument discovery", () => {
  describe("with a src/ directory", () => {
    useTempProject("lakatos-cli-zerosrc-", {
      "src/qux.ts": `/** @ensures{pos} forall (n: nat) { qux(n) >= 0 } */\nexport function qux(n: number): number { return n; }\n`,
      "src/types.d.ts": `export declare function qux(n: number): number;\n`,
    });

    it("discovers src/ sources and announces the discovery", () => {
      const { code, stdout, stderr } = runMain(["check"]);
      expect(code).toBe(1);
      expect(stderr[0]).toBe(
        "lakatos: no files given; discovered 1 file(s) via src/",
      );
      expect(JSON.parse(stdout[0]!).annotations).toHaveLength(1);
    });
  });

  describe("with a tsconfig.json", () => {
    useTempProject("lakatos-cli-zerotsc-", {
      "tsconfig.json": JSON.stringify({ include: ["lib"] }),
      "lib/qux.ts": `/** @ensures{pos} forall (n: nat) { qux(n) >= 0 } */\nexport function qux(n: number): number { return n; }\n`,
      "src/decoy.ts": `export function decoy(): number { return 1; }\n`,
    });

    it("discovers via tsconfig.json, not src/", () => {
      const { code, stdout, stderr } = runMain(["check"]);
      expect(code).toBe(1);
      expect(stderr[0]).toBe(
        "lakatos: no files given; discovered 1 file(s) via tsconfig.json",
      );
      expect(JSON.parse(stdout[0]!).annotations).toHaveLength(1);
    });
  });

  describe("with a malformed tsconfig.json", () => {
    useTempProject("lakatos-cli-zerobad-", {
      "tsconfig.json": JSON.stringify({ extends: "./missing.json" }),
      "src/a.ts": `export const a = 1;\n`,
    });

    it("exits 2 with the tsconfig diagnostic, not falling through", () => {
      const { code, stderr } = runMain(["check"]);
      expect(code).toBe(2);
      expect(stderr).toHaveLength(1);
      expect(stderr[0]).toContain("error: tsconfig.json:");
    });
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
  expected: string[];
}

const COMPILE_ERROR_CASES: CompileErrorCase[] = [
  {
    name: "a malformed quantifier prefix (prefix-parser)",
    file: "malformed.ts",
    source: `/** @ensures{shapely} for every (n: nat), malformed(n) >= 0 */\nexport function malformed(n: number): number { return n; }\n`,
    wrapped: true,
    property: "shapely",
    expected: ["expected 'forall'"],
  },
  {
    name: "an unexported-symbol reference (free-idents)",
    file: "unexported.ts",
    source: `/** @ensures{agrees} forall (n: nat) { unexported(n) === helper(n) } */\nexport function unexported(n: number): number { return n; }\nfunction helper(n: number): number { return n; }\n`,
    wrapped: true,
    property: "agrees",
    expected: ["'helper'", "not exported"],
  },
  {
    name: "a leading existential quantifier (prefix-parser)",
    file: "existential.ts",
    source: `/** @ensures{someone} exists (n: nat), ex(n) > 0 */\nexport function ex(n: number): number { return n; }\n`,
    wrapped: true,
    property: "someone",
    expected: ["existential quantifiers"],
  },
  {
    name: "an unresolvable domain (class-domain resolution)",
    file: "baddomain.ts",
    source: `/** @ensures{rounds} forall (x: float) { rounder(x) >= 0 } */\nexport function rounder(x: number): number { return x; }\n`,
    wrapped: true,
    property: "rounds",
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
    expected: ["existential quantifiers"],
  },
  {
    name: "a nested forall inside the body (formula-lexer)",
    file: "nestedforall.ts",
    source: `/** @ensures{deep} forall (n: nat) { forall (m: nat) { nested(n) >= 0 } } */\nexport function nested(n: number): number { return n; }\n`,
    wrapped: true,
    property: "deep",
    expected: ["nested quantifiers"],
  },
  {
    name: "JS && at the property's top level (formula-parser)",
    file: "jsconj.ts",
    source: `/** @ensures{conj} forall (n: nat) { jsconj(n) >= 0 && jsconj(n) >= 0 } */\nexport function jsconj(n: number): number { return n; }\n`,
    wrapped: true,
    property: "conj",
    expected: ["use ∧ for conjunction"],
  },
];

describe("cli compile errors (exit-code contract)", () => {
  useTempProject(
    "lakatos-cli-err-",
    Object.fromEntries(COMPILE_ERROR_CASES.map((c) => [c.file, c.source])),
  );

  it.each(COMPILE_ERROR_CASES)(
    "refute on $name exits 2 with a one-line diagnostic",
    (c) => {
      const { code, stderr } = runMain(["refute", c.file]);
      expect(code).toBe(2);
      const diagnostics = withoutSkipWarning(stderr);
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
});

// README usage claims: `lakatos refute` prints a single JSON envelope to
// stdout, exits 0/1 on clean/failing runs, echoes the seed, and reproduces a
// run when the seed is passed back. The generated tests import
// "lakatos/runtime" via the package self-reference, so these must run inside
// the repo tree (a gitignored scratch dir under .lakatos/), unlike the
// os.tmpdir()-based suites above.
describe("cli refute command (README usage claims)", () => {
  const workDir = path.join(repoRoot, ".lakatos", "clitest");

  beforeAll(() => {
    fs.rmSync(workDir, { recursive: true, force: true });
    fs.mkdirSync(workDir, { recursive: true });
    fs.writeFileSync(
      path.join(workDir, "good.ts"),
      `/** @ensures{nonneg} forall (n: nat) { good(n) >= 0 } */\nexport function good(n: number): number { return n; }\n`,
      "utf8",
    );
    fs.writeFileSync(
      path.join(workDir, "bad.ts"),
      `/** @ensures{negative} forall (n: nat) { bad(n) < 0 } */\nexport function bad(n: number): number { return n; }\n`,
      "utf8",
    );
    fs.writeFileSync(
      path.join(workDir, "plain.ts"),
      `export function plain(n: number): number { return n; }\n`,
      "utf8",
    );
    // In a subdirectory: the `*.ts` glob case below counts the top-level
    // fixtures, and a fourth one there would change its arithmetic.
    fs.mkdirSync(path.join(workDir, "klass"), { recursive: true });
    fs.writeFileSync(
      path.join(workDir, "klass", "box.ts"),
      `export class Box {
  #v: number;
  constructor(v: number) {
    this.#v = v;
  }
  /** @ensures{roundTrip} forall (x: number) { Object.is(new Box(x).v, x) } */
  get v(): number {
    return this.#v;
  }
}
`,
      "utf8",
    );
    fs.mkdirSync(path.join(workDir, "inputerr"), { recursive: true });
    fs.writeFileSync(
      path.join(workDir, "inputerr", "mixed.ts"),
      `class Hidden {
  /** @ensures{p} forall (x: int) { Hidden.id(x) === x } */
  static id(x: number): number { return x; }
}

/** @ensures{q} forall (x: int ∈ [0, 5)) { ok(x) === x } */
export function ok(x: number): number { return x; }
`,
      "utf8",
    );
    process.chdir(workDir);
  });
  afterAll(() => {
    process.chdir(repoRoot);
    fs.rmSync(workDir, { recursive: true, force: true });
  });
  // Each test starts from a clean mirror; the tests that exercise stale
  // mirrors create their own staleness within the test body.
  beforeEach(() => {
    fs.rmSync(path.join(workDir, RUN_ROOT), { recursive: true, force: true });
  });

  it(
    "refute still evaluates sound annotations beside InputError entries",
    { timeout: 60000 },
    () => {
      const { code, stdout } = runMain(["refute", "inputerr/mixed.ts"]);
      expect(code).toBe(2);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      const byProperty = Object.fromEntries(
        env.annotations.map((a: { property: string; szs: string }) => [
          a.property,
          a.szs,
        ]),
      );
      expect(byProperty).toEqual({ p: "InputError", q: "GaveUp" });
      expect(env.generated).toBe(1);
    },
  );

  it(
    "refute runs an @ensures attached to a getter under Class#getter",
    { timeout: 60000 },
    () => {
      const { code, stdout } = runMain(["refute", "klass/box.ts"]);
      expect(code).toBe(0);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env).toMatchObject({
        generated: 1,
        passed: 1,
        failed: 0,
        annotations: [
          {
            file: "klass/box.ts",
            function: "Box#v",
            property: "roundTrip",
            szs: "GaveUp",
          },
        ],
      });
    },
  );

  it(
    "refute on a clean file prints one JSON envelope to stdout and exits 0",
    { timeout: 60000 },
    () => {
      const { code, stdout } = runMain(["refute", "good.ts"]);
      expect(code).toBe(0);
      expect(stdout).toHaveLength(1);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      const pkg = JSON.parse(
        fs.readFileSync(path.join(repoRoot, "package.json"), "utf8"),
      );
      expect(env).toMatchObject({
        version: pkg.version,
        cwd: process.cwd(),
        generated: 1,
        passed: 1,
        failed: 0,
        annotations: [
          {
            file: "good.ts",
            function: "good",
            property: "nonneg",
            szs: "GaveUp",
          },
        ],
      });
      expect(env.annotations[0].kind).toBeUndefined();
      expect(env.startedAt).toMatch(
        /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d{3}Z$/,
      );
      expect(Number.isInteger(env.seed)).toBe(true);
      expect(env.seed).toBeGreaterThanOrEqual(0);
      expect(env.seed).toBeLessThan(2 ** 32);
    },
  );

  it(
    "refute on a failing file exits 1 with a flagged annotation in the envelope",
    { timeout: 60000 },
    () => {
      const { code, stdout } = runMain(["refute", "bad.ts"]);
      expect(code).toBe(1);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env).toMatchObject({ generated: 1, passed: 0, failed: 1 });
      expect(env.annotations).toHaveLength(1);
      expect(env.annotations[0]).toMatchObject({
        function: "bad",
        property: "negative",
        szs: "CounterSatisfiable",
        kind: "falsified",
      });
    },
  );

  it(
    "refute lets an input error take exit-code precedence over a refutation",
    { timeout: 60000 },
    () => {
      const { code, stdout } = runMain([
        "refute",
        "inputerr/mixed.ts",
        "bad.ts",
      ]);
      expect(code).toBe(2);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env.failed).toBe(1);
      const byProperty = Object.fromEntries(
        env.annotations.map((a: { property: string; szs: string }) => [
          a.property,
          a.szs,
        ]),
      );
      expect(byProperty).toMatchObject({
        p: "InputError",
        negative: "CounterSatisfiable",
      });
    },
  );

  it(
    "refute --seed echoes the given seed in the envelope",
    { timeout: 60000 },
    () => {
      const { code, stdout } = runMain(["refute", "--seed", "123", "good.ts"]);
      expect(code).toBe(0);
      expect(JSON.parse(stdout[0]!).seed).toBe(123);
    },
  );

  it(
    "passing a prior run's seed back reproduces that run",
    { timeout: 120000 },
    () => {
      const first = JSON.parse(runMain(["refute", "bad.ts"]).stdout[0]!);
      // Two degenerate runs would agree; pin that the baseline refuted before
      // comparing, so a degenerate baseline names itself instead of reading
      // like a seed bug.
      expect(first.annotations).toMatchObject([
        { szs: "CounterSatisfiable", kind: "falsified" },
      ]);
      fs.rmSync(path.join(workDir, RUN_ROOT), { recursive: true, force: true });
      const second = JSON.parse(
        runMain(["refute", "--seed", String(first.seed), "bad.ts"]).stdout[0]!,
      );
      expect(second.seed).toBe(first.seed);
      expect(second.annotations).toEqual(first.annotations);
      expect(second.passed).toBe(first.passed);
      expect(second.failed).toBe(first.failed);
    },
  );

  it(
    "refute's generated tests land under the run directory the envelope names",
    { timeout: 120000 },
    () => {
      const { code, stderr } = runMain(["refute", "good.ts"]);
      expect(code).toBe(0);
      const runDir = announcedRunDir(stderr);
      expect(
        fs.existsSync(path.join(runDir, "pabst", "good.ts.pabst.test.ts")),
      ).toBe(true);
      // vitest's own results are this run's business, not a sibling's.
      expect(
        fs.existsSync(path.join(runDir, "pabst", "vitest-results.json")),
      ).toBe(true);
    },
  );

  // The vitest run must be scoped to the out-files generated by THIS
  // invocation, not to every run directory sitting beside it.
  it(
    "back-to-back invocations do not leak issues from earlier runs",
    { timeout: 120000 },
    () => {
      expect(runMain(["refute", "bad.ts"]).code).toBe(1);
      // No wipe in between: bad.ts's own run directory is still there.
      const { code, stdout } = runMain(["refute", "good.ts"]);
      expect(code).toBe(0);
      const env = JSON.parse(stdout[0]!);
      expect(env).toMatchObject({
        generated: 1,
        passed: 1,
        failed: 0,
        annotations: [{ file: "good.ts", szs: "GaveUp" }],
      });
    },
  );

  it(
    "a run that generates nothing reports a zero envelope, never stale mirrors",
    { timeout: 120000 },
    () => {
      expect(runMain(["refute", "bad.ts"]).code).toBe(1);
      const { code, stdout } = runMain(["refute", "plain.ts"]);
      expect(code).toBe(0);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env).toMatchObject({
        generated: 0,
        passed: 0,
        failed: 0,
        annotations: [],
      });
    },
  );

  // End-to-end unhealthy run, no mocks: the module throws at load, so the
  // generated test can't even import it — vitest reports a file-level
  // failure with zero counted tests.
  it(
    "refute on a module that explodes at load prints a NotTried envelope and exits 2",
    { timeout: 60000 },
    () => {
      const explosive = path.join(workDir, "explosive.ts");
      fs.writeFileSync(
        explosive,
        `/** @ensures{pos} forall (n: nat) { boom(n) >= 0 } */\nexport function boom(n: number): number { return n; }\nthrow new Error("boom: module exploded");\n`,
        "utf8",
      );
      try {
        const { code, stdout, stderr } = runMain(["refute", "explosive.ts"]);
        expect(code).toBe(2);
        expect(stdout).toHaveLength(1);
        const env = JSON.parse(stdout[0]!);
        expectValidEnvelope(env);
        expect(env).toMatchObject({ generated: 1 });
        expect(env.annotations).toEqual([
          {
            file: "explosive.ts",
            function: "boom",
            property: "pos",
            szs: "NotTried",
          },
        ]);
        expect(stderr.join("\n")).toContain("boom: module exploded");
      } finally {
        fs.rmSync(explosive, { force: true });
      }
    },
  );

  it(
    "refute accepts globs and reports across all matched files",
    { timeout: 60000 },
    () => {
      const { code, stdout } = runMain(["refute", "*.ts"]);
      expect(code).toBe(1);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env).toMatchObject({ generated: 2, passed: 1, failed: 1 });
      const flagged = env.annotations.filter(
        (a: { kind?: string }) => a.kind !== undefined,
      );
      expect(flagged).toHaveLength(1);
    },
  );
});
