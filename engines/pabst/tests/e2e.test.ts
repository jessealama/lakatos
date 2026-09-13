import { describe, it, expect, afterAll, beforeAll } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { generate, type GenResult } from "../src/codegen.js";
import { runTests } from "../src/run.js";
import type { Issue } from "../src/contract.js";
import { buildEnvelope, type Envelope } from "../../../src/envelope.js";
import { expectValidIssue } from "./helpers/issue-schema.js";
import { expectValidEnvelope } from "../../../tests/helpers/envelope-schema.js";
import { META } from "./helpers/fixtures.js";

const root = process.cwd();
const passSrc = path.join(root, "engines/pabst/tests/fixtures/e2e/pass.ts");
const failSrc = path.join(root, "engines/pabst/tests/fixtures/e2e/fail.ts");
const commutesSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/commutes.ts",
);
const classPassSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/class-pass.ts",
);
const classFailSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/class-fail.ts",
);
const binderPassSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/binder-pass.ts",
);
const binderFailSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/binder-fail.ts",
);
const binderNestedPassSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/binder-nested-pass.ts",
);
const binderNestedFailSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/binder-nested-fail.ts",
);
const binderNestedExhaustedSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/binder-nested-exhausted.ts",
);
const accessorPassSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/accessor-pass.ts",
);
const accessorFailSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/accessor-fail.ts",
);
const nearMissSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/near-miss.ts",
);
const stringLawsSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/string-laws.ts",
);
const intRoundTripSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/int-round-trip.ts",
);
const floatAssocSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/float-associativity.ts",
);
const parseRoundTripSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/parse-round-trip.ts",
);
const safeSqrtSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/safe-sqrt.ts",
);
const boundedSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/bounded.ts",
);
const regexGuardSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/regex-guard.ts",
);
const equationPassSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/equation-pass.ts",
);
const equationFailSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/equation-fail.ts",
);
const exhaustedSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/precondition-exhausted.ts",
);
const throwingGuardSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/throwing-guard.ts",
);
const connectivesSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/connectives.ts",
);
const atomNotBoolSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/atom-not-boolean.ts",
);
const readmeExampleSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/readme-example.ts",
);
const enumeratedPassSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-pass.ts",
);
const enumeratedFailSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-fail.ts",
);
const enumeratedVacuousSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-vacuous.ts",
);
const enumeratedBudgetSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-budget.ts",
);
const enumeratedSlowOneSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-slow-one.ts",
);
// Tens of milliseconds: enough for the budget fixtures to overrun without
// making the suite wait on them.
const SHORT_BUDGET = { loopBudgetMs: 40 };

const enumeratedCapSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-cap.ts",
);
const enumeratedClassPassSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-class-pass.ts",
);
const enumeratedClassFailSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-class-fail.ts",
);
// The generated tests import "lakatos/runtime" via the package
// self-reference, so they must live inside the repo tree; this suite gets its
// own root there rather than sharing one with a CLI run.
const OUT_ROOT = ".lakatos/pabst-e2e";
const genDir = path.join(root, OUT_ROOT, "engines/pabst/tests/fixtures/e2e");

function clean(): void {
  fs.rmSync(genDir, { recursive: true, force: true });
}

const E2E_RESULTS = path.join(OUT_ROOT, "vitest-results.json");

function run(gen: GenResult): Envelope {
  const result = runTests(gen.outFile!, E2E_RESULTS);
  if (result.kind !== "completed") {
    throw new Error(`vitest run failed: ${JSON.stringify(result)}`);
  }
  const env = buildEnvelope(
    META,
    result.json,
    gen.properties.map((p) => ({ file: gen.sourceFile, ...p })),
  );
  expectValidEnvelope(env);
  return env;
}

/** The flagged annotations, reshaped as bare issues for the pinned checks.
 * An enumerated Theorem carries a kind too, and is not an issue. */
function issuesOf(env: Envelope): Issue[] {
  return env.annotations
    .filter((a) => a.kind !== undefined && a.kind !== "enumerated")
    .map(({ szs, ...issue }) => issue as Issue);
}

/** One generate and one child run over every batched fixture; rows read
 * their own file's annotations out of the shared envelope. */
function runBatch(
  files: string[],
  seed: number,
): { env: Envelope; gens: GenResult[] } {
  const gens = generate(files, OUT_ROOT, seed);
  expect(gens.map((g) => g.sourceFile)).toEqual(files);
  const result = runTests(
    gens.map((g) => g.outFile!),
    E2E_RESULTS,
  );
  if (result.kind !== "completed") {
    throw new Error(`vitest run failed: ${JSON.stringify(result)}`);
  }
  const env = buildEnvelope(
    META,
    result.json,
    gens.flatMap((g) =>
      g.properties.map((p) => ({ file: g.sourceFile, ...p })),
    ),
  );
  expectValidEnvelope(env);
  return { env, gens };
}

function forFile(env: Envelope, file: string): Envelope["annotations"] {
  return env.annotations.filter((a) => a.file === file);
}

function issuesFor(env: Envelope, file: string): Issue[] {
  return forFile(env, file)
    .filter((a) => a.kind !== undefined && a.kind !== "enumerated")
    .map(({ szs, ...issue }) => issue as Issue);
}

const SAMPLED_SEED = 3;
const SAMPLED_ROWS = [
  passSrc,
  classPassSrc,
  binderPassSrc,
  binderNestedPassSrc,
  accessorPassSrc,
  stringLawsSrc,
  intRoundTripSrc,
  regexGuardSrc,
  equationPassSrc,
  failSrc,
  commutesSrc,
  classFailSrc,
  binderFailSrc,
  binderNestedFailSrc,
  binderNestedExhaustedSrc,
  accessorFailSrc,
  nearMissSrc,
  readmeExampleSrc,
  parseRoundTripSrc,
  safeSqrtSrc,
  throwingGuardSrc,
  exhaustedSrc,
  equationFailSrc,
];

// Seed 3 is pinned: the -0 and x=0 rows each fail for a single input that
// fast-check does not reliably probe on a random seed; 3 is verified to
// probe 0 for fc.nat() and fc.double().
describe("end-to-end: sampled rows, seed 3", () => {
  let env: Envelope;
  let emittedRegexGuard: string;
  beforeAll(() => {
    clean();
    const batch = runBatch(SAMPLED_ROWS, SAMPLED_SEED);
    env = batch.env;
    const regexGuardGen = batch.gens.find(
      (g) => g.sourceFile === regexGuardSrc,
    );
    emittedRegexGuard = fs.readFileSync(regexGuardGen!.outFile!, "utf8");
  }, 60000);
  afterAll(clean);

  it("a true property passes vitest", () => {
    expect(issuesFor(env, passSrc)).toEqual([]);
  });

  it("a false property fails vitest with a structured counterexample", () => {
    const issues = issuesFor(env, failSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      property: "wrong",
      kind: "falsified",
      counterexample: { x: 1 },
    });
  });

  it("a two-binder commutativity claim is falsified with both binders bound", () => {
    const issues = issuesFor(env, commutesSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "f",
      property: "commutes",
      kind: "falsified",
      counterexample: { a: 0, b: 1 },
    });
  });

  it("class instance + static properties that hold pass vitest", () => {
    expect(issuesFor(env, classPassSrc)).toEqual([]);
  });

  it("a buggy instance method is flagged as Class#method", () => {
    const issues = issuesFor(env, classFailSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "BoundedCounter#dec",
      property: "neverNegative",
      kind: "falsified",
      counterexample: { x: 0 },
    });
  });

  it("a true property over class binders passes: throwing tuples discard", () => {
    expect(issuesFor(env, binderPassSrc)).toEqual([]);
  });

  it("a false property over class binders reports constructions as the counterexample", () => {
    const issues = issuesFor(env, binderFailSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "Point#distance",
      property: "tight",
      kind: "falsified",
    });
    const cx = (issues[0] as { counterexample: Record<string, string> })
      .counterexample;
    expect(cx.p).toMatch(/^new Point\(/);
    expect(cx.q).toMatch(/^new Point\(/);
  });

  it("a true property over a nested class binder passes", () => {
    expect(issuesFor(env, binderNestedPassSrc)).toEqual([]);
  });

  it("a nested counterexample reports the whole construction tree", () => {
    const issues = issuesFor(env, binderNestedFailSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "Span#length",
      property: "tight",
      kind: "falsified",
    });
    const cx = (issues[0] as { counterexample: Record<string, string> })
      .counterexample;
    expect(cx.s).toMatch(/^new Span\(new Point\(.+\),new Point\(.+\)\)$/);
  });

  it("compounded constructor discards are reported as kind 'exhausted'", () => {
    const issues = issuesFor(env, binderNestedExhaustedSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      property: "onTheMark",
      kind: "exhausted",
    });
    expect(issues[0]!.counterexample).toBeUndefined();
  });

  it("getter and constructor properties that hold pass vitest", () => {
    expect(issuesFor(env, accessorPassSrc)).toEqual([]);
    // Both attachment points ran: the getter and the constructor.
    expect(
      forFile(env, accessorPassSrc)
        .map((a) => a.function)
        .sort(),
    ).toEqual(["Box#constructor", "Box#v"]);
  });

  it("a buggy getter is flagged as Class#getter", () => {
    const issues = issuesFor(env, accessorFailSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "ClampedBox#v",
      property: "roundTrip",
      kind: "falsified",
    });
  });

  it("a static-method near-miss is flagged as Class.method with the -0 counterexample", () => {
    const issues = issuesFor(env, nearMissSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "Arith.negate",
      property: "matchesSubtraction",
      kind: "falsified",
      counterexample: { x: 0 },
    });
  });

  it("the README front-page example is verbatim on disk and is falsified", () => {
    const readme = fs.readFileSync(
      path.join(root, "engines/pabst/README.md"),
      "utf8",
    );
    const block = /```ts\n([\s\S]*?)```/.exec(readme)?.[1];
    expect(block, "README has no ```ts code block").toBeDefined();
    expect(
      fs.readFileSync(readmeExampleSrc, "utf8"),
      "engines/pabst/tests/fixtures/e2e/readme-example.ts must be byte-identical to the README's first ts block",
    ).toBe(block);
    const issues = issuesFor(env, readmeExampleSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "foo",
      property: "nonzero",
      kind: "falsified",
    });
    expect(Object.keys(issues[0]!.counterexample ?? {})).toEqual(["x", "y"]);
  });

  it("README string laws (contains) pass vitest", () => {
    expect(issuesFor(env, stringLawsSrc)).toEqual([]);
  });

  it("Number(String(x)) round-trips over int", () => {
    expect(issuesFor(env, intRoundTripSrc)).toEqual([]);
  });

  it("parseInt is NOT the inverse of String over doubles (falsified)", () => {
    const issues = issuesFor(env, parseRoundTripSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      property: "parseIntInverts",
      kind: "falsified",
    });
    expect(Object.keys(issues[0]!.counterexample ?? {})).toEqual(["x"]);
  });

  it("a property whose body throws is reported as kind 'threw'", () => {
    const issues = issuesFor(env, safeSqrtSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      property: "nonNegativeRoot",
      kind: "threw",
    });
    expect(issues[0]!.error).toContain("negative");
    expect(Object.keys(issues[0]!.counterexample ?? {})).toEqual(["x"]);
  });

  it("a guard that throws is reported as kind 'threw', not discarded", () => {
    // The prover reads the same thrown guard as a failed `= pure true`
    // hypothesis — vacuous truth. Divergence documented on both sides.
    const issues = issuesFor(env, throwingGuardSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      property: "guardThrows",
      kind: "threw",
    });
    expect(issues[0]!.error).toContain("negative");
  });

  it("an unsatisfiable precondition is reported as kind 'exhausted'", () => {
    const issues = issuesFor(env, exhaustedSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      property: "unsatisfiable",
      kind: "exhausted",
    });
    expect(issues[0]!.counterexample).toBeUndefined();
  });

  it("regex-guarded string binders only generate matching values", () => {
    // Pin the emitted arbitraries: anchored, non-capturing, flags kept.
    expect(emittedRegexGuard).toContain("fc.stringMatching(/^(?:[a-z]+)$/)");
    expect(emittedRegexGuard).toContain(
      "fc.stringMatching(/^(?:\\p{Lu}{2,5})$/u)",
    );
    expect(issuesFor(env, regexGuardSrc)).toEqual([]);
  });

  it("equation syntax: guarded identities pass vitest", () => {
    expect(issuesFor(env, equationPassSrc)).toEqual([]);
  });

  it("equation syntax: the -0 near-miss is refuted via ≡", () => {
    const issues = issuesFor(env, equationFailSrc);
    expect(issues).toHaveLength(1);
    expectValidIssue(issues[0]);
    expect(issues[0]).toMatchObject({
      function: "negate",
      property: "matchesSubtraction",
      kind: "falsified",
      counterexample: { x: 0 },
    });
  });
});

describe("end-to-end", () => {
  beforeAll(clean);
  afterAll(clean);

  it(
    "float addition is NOT associative (falsified)",
    { timeout: 30000 },
    () => {
      const [r] = generate([floatAssocSrc], OUT_ROOT, 1);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        property: "associative",
        kind: "falsified",
      });
      expect(Object.keys(issuesOf(env)[0]!.counterexample ?? {})).toEqual([
        "x",
        "y",
        "z",
      ]);
    },
  );

  it(
    "interval-bounded binders only generate in-range values",
    { timeout: 30000 },
    () => {
      const [r] = generate([boundedSrc], OUT_ROOT);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
      const by = new Map(env.annotations.map((a) => [a.property, a]));
      expect(by.get("staysInRange")).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 30,
      });
      expect(by.get("bigintBounds")).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 101,
      });
      expect(by.get("halfOpenInt")).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 10,
      });
      expect(by.get("bigintOpen")).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 100,
      });
      expect(by.get("clampedNat")).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 6,
      });
      for (const p of [
        "unitInterval",
        "strictlyPositive",
        "positiveNat",
        "farOutOneSided",
        "halfOpenAtZero",
      ])
        expect(by.get(p)).toMatchObject({ szs: "GaveUp" });
    },
  );

  it(
    "a small domain walked in full is a Theorem with its case count",
    { timeout: 30000 },
    () => {
      const [r] = generate([enumeratedPassSrc], OUT_ROOT);
      const env = run(r!);
      expect(env).toMatchObject({ passed: 1, failed: 0 });
      expect(env.annotations).toEqual([
        {
          file: enumeratedPassSrc,
          function: "square",
          property: "pos",
          szs: "Theorem",
          kind: "enumerated",
          cases: 10,
        },
      ]);
      expect(fs.readFileSync(r!.outFile!, "utf8")).not.toContain("test.prop(");
    },
  );

  it(
    "a walked domain reports the least counterexample, and a throw with its tuple",
    { timeout: 30000 },
    () => {
      const [r] = generate([enumeratedFailSrc], OUT_ROOT);
      const env = run(r!);
      expect(env.failed).toBe(2);
      const by = new Map(env.annotations.map((a) => [a.property, a]));
      expect(by.get("noThree")).toMatchObject({
        szs: "CounterSatisfiable",
        kind: "falsified",
        counterexample: { a: 0, b: 3 },
      });
      expect(by.get("rootDefined")).toMatchObject({
        szs: "Error",
        kind: "threw",
        counterexample: { n: -2 },
        error: "negative: -2",
      });
      for (const issue of issuesOf(env)) expectValidIssue(issue);
    },
  );

  it(
    "a domain the preconditions discard entirely is a vacuous Theorem",
    { timeout: 30000 },
    () => {
      const [r] = generate([enumeratedVacuousSrc], OUT_ROOT);
      const env = run(r!);
      expect(env.annotations[0]).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 10,
      });
    },
  );

  it(
    "a class binder whose constructor slots are all finite is walked in full",
    { timeout: 30000 },
    () => {
      const [r] = generate([enumeratedClassPassSrc], OUT_ROOT);
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
      const by = new Map(env.annotations.map((a) => [a.property, a]));
      const walked = (cases: number) => ({
        szs: "Theorem",
        kind: "enumerated",
        cases,
      });
      expect(by.get("sound")).toMatchObject(walked(4));
      expect(by.get("unit")).toMatchObject(walked(1));
      expect(by.get("nested")).toMatchObject(walked(16));
      expect(by.get("mixed")).toMatchObject(walked(8));
      // A rejected tuple is skipped yet counted; a class every tuple of
      // which is rejected is walked to a vacuous Theorem.
      expect(by.get("partialThrow")).toMatchObject(walked(4));
      expect(by.get("allThrow")).toMatchObject(walked(2));
      expect(by.get("sampled")).toMatchObject({ szs: "GaveUp" });
      expect(by.get("sampled")!.cases).toBeUndefined();
    },
  );

  it(
    "a falsified class binder renders the least tuple as its construction",
    { timeout: 30000 },
    () => {
      const [r] = generate([enumeratedClassFailSrc], OUT_ROOT);
      const env = run(r!);
      expect(env.failed).toBe(2);
      const by = new Map(env.annotations.map((a) => [a.property, a]));
      expect(by.get("onIsLive")).toMatchObject({
        function: "isLive",
        szs: "CounterSatisfiable",
        kind: "falsified",
        counterexample: { f: "new Flag(true,false)" },
      });
      expect(by.get("leftLeads")).toMatchObject({
        szs: "CounterSatisfiable",
        kind: "falsified",
        counterexample: {
          p: "new Pair(new Flag(false,false),new Flag(true,true))",
        },
      });
      for (const issue of issuesOf(env)) expectValidIssue(issue);
    },
  );

  it(
    "a walk that outruns its budget is a Timeout saying how far it got",
    { timeout: 30000 },
    () => {
      const [r] = generate(
        [enumeratedBudgetSrc],
        OUT_ROOT,
        undefined,
        new Set(),
        SHORT_BUDGET,
      );
      const env = run(r!);
      expect(env.failed).toBe(1);
      const a = env.annotations[0]!;
      expect(a).toMatchObject({ szs: "Timeout", kind: "budget" });
      expect(a.reason).toMatch(
        /^evaluated \d+ of 1000 cases within the time budget, no counterexample$/,
      );
      const evaluated = Number(/evaluated (\d+)/.exec(a.reason!)![1]);
      expect(evaluated).toBeGreaterThan(0);
      expect(evaluated).toBeLessThan(1000);
      expectValidIssue(issuesOf(env)[0]);
    },
  );

  it(
    "a walk whose only tuple outruns the budget still finishes as a Theorem",
    { timeout: 30000 },
    () => {
      const [r] = generate(
        [enumeratedSlowOneSrc],
        OUT_ROOT,
        undefined,
        new Set(),
        SHORT_BUDGET,
      );
      const env = run(r!);
      expect(env).toMatchObject({ passed: 1, failed: 0 });
      expect(env.annotations).toHaveLength(1);
      expect(env.annotations[0]).toMatchObject({
        function: "crawl",
        property: "slow",
        szs: "Theorem",
        kind: "enumerated",
        cases: 1,
      });
    },
  );

  it(
    "the cap: 1000 tuples walk, 1001 sample exactly as before",
    { timeout: 30000 },
    () => {
      const [r] = generate([enumeratedCapSrc], OUT_ROOT);
      expect(r!.properties).toEqual([
        { function: "keep", property: "atCap", cases: 1000 },
        { function: "hold", property: "aboveCap" },
      ]);
      const code = fs.readFileSync(r!.outFile!, "utf8");
      expect(code).toContain('test("atCap", { timeout: 0 }');
      expect(code).toContain("test.prop([fc.integer({ min: 0, max: 1000 })]");
      const env = run(r!);
      const by = new Map(env.annotations.map((a) => [a.property, a]));
      expect(by.get("atCap")).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 1000,
      });
      expect(by.get("aboveCap")).toEqual({
        file: enumeratedCapSrc,
        function: "hold",
        property: "aboveCap",
        szs: "GaveUp",
      });
    },
  );
});

describe("e2e — math-y connectives", () => {
  afterAll(clean);

  it(
    "passes a De Morgan biconditional and a guarded implication",
    { timeout: 30000 },
    () => {
      clean();
      const [res] = generate([connectivesSrc], OUT_ROOT, 1234);
      const env = run(res!);
      expect(issuesOf(env)).toEqual([]);
      expect(env.failed).toBe(0);
      const by = new Map(env.annotations.map((a) => [a.property, a]));
      expect(by.get("deMorgan")).toMatchObject({
        szs: "Theorem",
        kind: "enumerated",
        cases: 4,
      });
      expect(by.get("guarded")).toMatchObject({ szs: "GaveUp" });
    },
  );

  it(
    "reports a threw issue naming a non-boolean atom",
    { timeout: 30000 },
    () => {
      clean();
      const [res] = generate([atomNotBoolSrc], OUT_ROOT, 1234);
      const env = run(res!);
      const issue = issuesOf(env).find((i) => i.property === "notBool");
      expect(issue?.kind).toBe("threw");
      expect(issue?.error).toMatch(
        /atom "addOne\(x\)" evaluated to .*not a boolean/,
      );
      expectValidIssue(issue);
    },
  );
});
