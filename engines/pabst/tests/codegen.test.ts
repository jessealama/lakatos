import { describe, it, expect, afterAll, beforeAll } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { generate } from "../src/codegen.js";
import { PabstError } from "../src/errors.js";

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
    const results = generate(["bar.ts"], ".pabst", 7);
    expect(results).toHaveLength(1);
    expect(results[0]!.properties).toEqual([
      { function: "bar", property: "pos" },
    ]);
    expect(results[0]!.outFile).toBe(path.join(".pabst", "bar.pabst.test.ts"));
    expect(fs.existsSync(results[0]!.outFile)).toBe(true);
    const code = fs.readFileSync(results[0]!.outFile, "utf8");
    expect(code).toContain(
      'test.prop([fc.nat()], { seed: 7, reporter: (d) => __pabstReport("bar.ts", "bar", "pos", ["n"], d) })("pos"',
    );
    expect(code).toContain("const { bar } = __M;");
  });

  it("reports each generated property's qualified identity in order", () => {
    const [r] = generate(["multi.ts"], ".pabst", 7);
    expect(r!.properties).toEqual([
      { function: "abs", property: "nonneg" },
      { function: "Counter#bump", property: "grows" },
    ]);
  });

  it("skips a file with no @ensures annotations", () => {
    const results = generate(["plain.ts"], ".pabst", 7);
    expect(results).toEqual([]);
    expect(fs.existsSync(path.join(".pabst", "plain.pabst.test.ts"))).toBe(
      false,
    );
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

  it("throws PabstError rather than writing outside the output root", () => {
    expect(() => generate(["../evil.ts"], ".pabst", 7)).toThrow(PabstError);
    expect(() => generate(["../evil.ts"], ".pabst", 7)).toThrow(
      /outside the current directory/,
    );
    // Nothing may leak into the tree: not under .pabst/, not beside it.
    expect(fs.existsSync(path.join(dir, "evil.pabst.test.ts"))).toBe(false);
    expect(fs.existsSync(path.join(dir, "pkg", ".pabst"))).toBe(false);
  });
});
