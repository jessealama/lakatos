import { describe, it, expect, afterAll, beforeAll } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { generate } from "../src/codegen.js";
import { LemmaError } from "../../../lemma/src/index.js";

// The out root is the caller's to choose; these tests pick an arbitrary
// one, since what is under test is the mirroring, not the CLI's naming.
const OUT = "out";

describe("generate", () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pabst-codegen-"));
  const prevCwd = process.cwd();

  beforeAll(() => {
    fs.writeFileSync(
      path.join(dir, "bar.ts"),
      `/** @ensures{pos} forall (n: nat) { bar(n) >= 0 } */\nexport function bar(n: number): number { return n; }\n`,
      "utf8",
    );
    fs.writeFileSync(
      path.join(dir, "small.ts"),
      `/** @ensures{pos} forall (n: int ∈ [1, 10]) { square(n) > 0 } */\nexport function square(n: number): number { return n * n; }\n`,
      "utf8",
    );
    fs.writeFileSync(
      path.join(dir, "plain.ts"),
      `export function plain(n: number): number { return n; }\n`,
      "utf8",
    );
    fs.writeFileSync(
      path.join(dir, "multi.ts"),
      `/** @ensures{nonneg} forall (x: int) { abs(x) >= 0 } */
export function abs(x: number): number { return x < 0 ? -x : x; }
export class Counter {
  constructor(private readonly n: number) {}
  /** @ensures{grows} forall (x: int) { new Counter(x).bump().value >= x } */
  bump(): Counter { return new Counter(this.n + 1); }
  get value(): number { return this.n; }
}
`,
      "utf8",
    );
    process.chdir(dir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(dir, { recursive: true, force: true });
  });

  it("writes one generated test file and reports the count", () => {
    const results = generate(["bar.ts"], OUT, 7);
    expect(results).toHaveLength(1);
    expect(results[0]!.properties).toEqual([
      { function: "bar", property: "pos" },
    ]);
    expect(results[0]!.outFile).toBe(path.join(OUT, "bar.ts.pabst.test.ts"));
    expect(fs.existsSync(results[0]!.outFile!)).toBe(true);
    const code = fs.readFileSync(results[0]!.outFile!, "utf8");
    expect(code).toContain(
      'test.prop([fc.nat()], { seed: 7, reporter: (d) => __pabstReport("bar.ts", "bar", "pos", ["n"], d) })("pos"',
    );
    expect(code).toContain("const { bar } = __M;");
  });

  it("reports each generated property's qualified identity in order", () => {
    const [r] = generate(["multi.ts"], OUT, 7);
    expect(r!.properties).toEqual([
      { function: "abs", property: "nonneg" },
      { function: "Counter#bump", property: "grows" },
    ]);
  });

  it("reports the case count of a property it will walk in full", () => {
    const [r] = generate(["small.ts"], OUT, 7);
    expect(r!.properties).toEqual([
      { function: "square", property: "pos", cases: 10 },
    ]);
    const code = fs.readFileSync(r!.outFile!, "utf8");
    expect(code).toContain('test("pos", { timeout: 8000 }');
  });

  it("skips a file with no @ensures annotations", () => {
    const results = generate(["plain.ts"], OUT, 7);
    expect(results).toEqual([]);
    expect(fs.existsSync(path.join(OUT, "plain.ts.pabst.test.ts"))).toBe(false);
  });
});

describe("generate: source outside the current directory", () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pabst-codegen-out-"));
  const prevCwd = process.cwd();

  beforeAll(() => {
    fs.mkdirSync(path.join(dir, "pkg"));
    fs.writeFileSync(
      path.join(dir, "evil.ts"),
      `/** @ensures{pos} forall (n: nat) { evil(n) >= 0 } */\nexport function evil(n: number): number { return n; }\n`,
      "utf8",
    );
    process.chdir(path.join(dir, "pkg"));
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(dir, { recursive: true, force: true });
  });

  it("throws LemmaError rather than writing outside the output root", () => {
    expect(() => generate(["../evil.ts"], OUT, 7)).toThrow(LemmaError);
    expect(() => generate(["../evil.ts"], OUT, 7)).toThrow(
      /outside the current directory/,
    );
    // Nothing may leak into the tree: not under the out root, not beside it.
    expect(fs.existsSync(path.join(dir, "evil.ts.pabst.test.ts"))).toBe(false);
    expect(fs.existsSync(path.join(dir, "pkg", OUT))).toBe(false);
  });
});

describe("generate — unrepresentable domains", () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pabst-untried-"));
  const prevCwd = process.cwd();

  beforeAll(() => {
    fs.writeFileSync(
      path.join(dir, "allhuge.ts"),
      `/** @ensures{huge} forall (n: int ∈ [0, 1000000000000000000000000000000]) { one(n) >= 0 } */\nexport function one(n: number): number { return n; }\n`,
      "utf8",
    );
    fs.writeFileSync(
      path.join(dir, "mixedhuge.ts"),
      `/** @ensures{huge} forall (n: int ∈ [0, 1000000000000000000000000000000]) { two(n) >= 0 }
 * @ensures{small} forall (n: int ∈ [0, 10]) { two(n) >= 0 } */
export function two(n: number): number { return n; }
`,
      "utf8",
    );
    process.chdir(dir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(dir, { recursive: true, force: true });
  });

  it("reports a wholly untried file without writing an artifact", () => {
    const results = generate(["allhuge.ts"], OUT, 7);
    expect(results).toHaveLength(1);
    expect(results[0]!.outFile).toBeUndefined();
    expect(results[0]!.properties).toEqual([]);
    expect(results[0]!.untried).toEqual([
      {
        function: "one",
        property: "huge",
        reason:
          "endpoint 1000000000000000000000000000000 exceeds " +
          "the safe integer range (±9007199254740991)",
      },
    ]);
    expect(fs.existsSync(path.join(OUT, "allhuge.ts.pabst.test.ts"))).toBe(
      false,
    );
  });

  it("generates only the testable properties of a mixed file", () => {
    const results = generate(["mixedhuge.ts"], OUT, 7);
    expect(results[0]!.properties).toEqual([
      { function: "two", property: "small", cases: 11 },
    ]);
    expect(results[0]!.untried.map((u) => u.property)).toEqual(["huge"]);
    const code = fs.readFileSync(results[0]!.outFile!, "utf8");
    expect(code).toContain('"small"');
    expect(code).not.toContain('"huge"');
  });
});
