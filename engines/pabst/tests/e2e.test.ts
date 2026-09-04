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
const enumeratedCapSrc = path.join(
  root,
  "engines/pabst/tests/fixtures/e2e/enumerated-cap.ts",
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

describe("end-to-end", () => {
  beforeAll(clean);
  afterAll(clean);

  it("a true property passes vitest", { timeout: 30000 }, () => {
    const [r] = generate([passSrc], OUT_ROOT);
    expect(r).toBeDefined();
    const env = run(r!);
    expect(env.failed).toBe(0);
    expect(issuesOf(env)).toEqual([]);
  });

  it(
    "a false property fails vitest with a structured counterexample",
    { timeout: 30000 },
    () => {
      const [r] = generate([failSrc], OUT_ROOT);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        property: "wrong",
        kind: "falsified",
        counterexample: { x: 1 },
      });
    },
  );

  it(
    "a two-binder commutativity claim is falsified with both binders bound",
    { timeout: 30000 },
    () => {
      const [r] = generate([commutesSrc], OUT_ROOT);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(issuesOf(env)).toHaveLength(1);
      const issue = issuesOf(env)[0]!;
      expectValidIssue(issue);
      expect(issue).toMatchObject({
        function: "f",
        property: "commutes",
        kind: "falsified",
        counterexample: { a: 0, b: 1 },
      });
    },
  );

  // Seed 3 is pinned: these fixtures each fail for a single input (x=0 / +0), and
  // fast-check does NOT reliably probe 0 on a random seed (~50% miss rate), so an
  // unseeded run is a coin flip. Seed 3 is verified to probe 0 for both fc.nat()
  // and fc.double().
  it(
    "class instance + static properties that hold pass vitest",
    { timeout: 30000 },
    () => {
      const [r] = generate([classPassSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
    },
  );

  it(
    "a buggy instance method is flagged as Class#method",
    { timeout: 30000 },
    () => {
      const [r] = generate([classFailSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        function: "BoundedCounter#dec",
        property: "neverNegative",
        kind: "falsified",
        counterexample: { x: 0 },
      });
    },
  );

  it(
    "a true property over class binders passes: throwing tuples discard",
    { timeout: 30000 },
    () => {
      const [r] = generate([binderPassSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
    },
  );

  it(
    "a false property over class binders reports constructions as the counterexample",
    { timeout: 30000 },
    () => {
      const [r] = generate([binderFailSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      const issue = issuesOf(env)[0]!;
      expect(issue).toMatchObject({
        function: "Point#distance",
        property: "tight",
        kind: "falsified",
      });
      const cx = (issue as { counterexample: Record<string, string> })
        .counterexample;
      expect(cx.p).toMatch(/^new Point\(/);
      expect(cx.q).toMatch(/^new Point\(/);
    },
  );

  it(
    "a true property over a nested class binder passes",
    { timeout: 30000 },
    () => {
      const [r] = generate([binderNestedPassSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
    },
  );

  it(
    "a nested counterexample reports the whole construction tree",
    { timeout: 30000 },
    () => {
      const [r] = generate([binderNestedFailSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      const issue = issuesOf(env)[0]!;
      expect(issue).toMatchObject({
        function: "Span#length",
        property: "tight",
        kind: "falsified",
      });
      const cx = (issue as { counterexample: Record<string, string> })
        .counterexample;
      expect(cx.s).toMatch(/^new Span\(new Point\(.+\),new Point\(.+\)\)$/);
    },
  );

  it(
    "compounded constructor discards are reported as kind 'exhausted'",
    { timeout: 30000 },
    () => {
      const [r] = generate([binderNestedExhaustedSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        property: "onTheMark",
        kind: "exhausted",
      });
      expect(issuesOf(env)[0]!.counterexample).toBeUndefined();
    },
  );

  it(
    "getter and constructor properties that hold pass vitest",
    { timeout: 30000 },
    () => {
      const [r] = generate([accessorPassSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
      // Both attachment points ran: the getter and the constructor.
      expect(env.annotations.map((a) => a.function).sort()).toEqual([
        "Box#constructor",
        "Box#v",
      ]);
    },
  );

  it("a buggy getter is flagged as Class#getter", { timeout: 30000 }, () => {
    const [r] = generate([accessorFailSrc], OUT_ROOT, 3);
    expect(r).toBeDefined();
    const env = run(r!);
    expect(env.failed).toBeGreaterThan(0);
    expect(issuesOf(env)).toHaveLength(1);
    expectValidIssue(issuesOf(env)[0]);
    expect(issuesOf(env)[0]).toMatchObject({
      function: "ClampedBox#v",
      property: "roundTrip",
      kind: "falsified",
    });
  });

  it(
    "a static-method near-miss is flagged as Class.method with the -0 counterexample",
    { timeout: 30000 },
    () => {
      const [r] = generate([nearMissSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        function: "Arith.negate",
        property: "matchesSubtraction",
        kind: "falsified",
        counterexample: { x: 0 },
      });
    },
  );

  it(
    "the README front-page example is verbatim on disk and is falsified",
    { timeout: 30000 },
    () => {
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
      const [r] = generate([readmeExampleSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        function: "foo",
        property: "nonzero",
        kind: "falsified",
      });
      expect(Object.keys(issuesOf(env)[0]!.counterexample ?? {})).toEqual([
        "x",
        "y",
      ]);
    },
  );

  it("README string laws (contains) pass vitest", { timeout: 30000 }, () => {
    const [r] = generate([stringLawsSrc], OUT_ROOT);
    expect(r).toBeDefined();
    const env = run(r!);
    expect(env.failed).toBe(0);
    expect(issuesOf(env)).toEqual([]);
  });

  it("Number(String(x)) round-trips over int", { timeout: 30000 }, () => {
    const [r] = generate([intRoundTripSrc], OUT_ROOT);
    expect(r).toBeDefined();
    const env = run(r!);
    expect(env.failed).toBe(0);
    expect(issuesOf(env)).toEqual([]);
  });

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
    "parseInt is NOT the inverse of String over doubles (falsified)",
    { timeout: 30000 },
    () => {
      const [r] = generate([parseRoundTripSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        property: "parseIntInverts",
        kind: "falsified",
      });
      expect(Object.keys(issuesOf(env)[0]!.counterexample ?? {})).toEqual([
        "x",
      ]);
    },
  );

  it(
    "a property whose body throws is reported as kind 'threw'",
    { timeout: 30000 },
    () => {
      const [r] = generate([safeSqrtSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        property: "nonNegativeRoot",
        kind: "threw",
      });
      expect(issuesOf(env)[0]!.error).toContain("negative");
      expect(Object.keys(issuesOf(env)[0]!.counterexample ?? {})).toEqual([
        "x",
      ]);
    },
  );

  it(
    "a guard that throws is reported as kind 'threw', not discarded",
    { timeout: 30000 },
    () => {
      // The prover reads the same thrown guard as a failed `= pure true`
      // hypothesis — vacuous truth. Divergence documented on both sides.
      const [r] = generate([throwingGuardSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        property: "guardThrows",
        kind: "threw",
      });
      expect(issuesOf(env)[0]!.error).toContain("negative");
    },
  );

  it(
    "an unsatisfiable precondition is reported as kind 'exhausted'",
    { timeout: 30000 },
    () => {
      const [r] = generate([exhaustedSrc], OUT_ROOT);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        property: "unsatisfiable",
        kind: "exhausted",
      });
      expect(issuesOf(env)[0]!.counterexample).toBeUndefined();
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
    "regex-guarded string binders only generate matching values",
    { timeout: 30000 },
    () => {
      const [r] = generate([regexGuardSrc], OUT_ROOT);
      expect(r).toBeDefined();
      // Pin the emitted arbitraries: anchored, non-capturing, flags kept.
      const emitted = fs.readFileSync(r!.outFile!, "utf8");
      expect(emitted).toContain("fc.stringMatching(/^(?:[a-z]+)$/)");
      expect(emitted).toContain("fc.stringMatching(/^(?:\\p{Lu}{2,5})$/u)");
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
    },
  );

  it(
    "equation syntax: guarded identities pass vitest",
    { timeout: 30000 },
    () => {
      const [r] = generate([equationPassSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBe(0);
      expect(issuesOf(env)).toEqual([]);
    },
  );

  it(
    "equation syntax: the -0 near-miss is refuted via ≡",
    { timeout: 30000 },
    () => {
      const [r] = generate([equationFailSrc], OUT_ROOT, 3);
      expect(r).toBeDefined();
      const env = run(r!);
      expect(env.failed).toBeGreaterThan(0);
      expect(issuesOf(env)).toHaveLength(1);
      expectValidIssue(issuesOf(env)[0]);
      expect(issuesOf(env)[0]).toMatchObject({
        function: "negate",
        property: "matchesSubtraction",
        kind: "falsified",
        counterexample: { x: 0 },
      });
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
    "a walk that outruns its budget is a Timeout saying how far it got",
    { timeout: 60000 },
    () => {
      const [r] = generate([enumeratedBudgetSrc], OUT_ROOT);
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
    "the cap: 1000 tuples walk, 1001 sample exactly as before",
    { timeout: 30000 },
    () => {
      const [r] = generate([enumeratedCapSrc], OUT_ROOT);
      expect(r!.properties).toEqual([
        { function: "keep", property: "atCap", cases: 1000 },
        { function: "hold", property: "aboveCap" },
      ]);
      const code = fs.readFileSync(r!.outFile!, "utf8");
      expect(code).toContain('test("atCap", { timeout: 8000 }');
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
