import { describe, it, expect, afterAll, beforeAll, beforeEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { clearRunDirs, seedRefuteProject } from "./helpers/refute-project.js";

const repoRoot = process.cwd();

// README usage claims: `lakatos refute` prints a single JSON envelope to
// stdout, exits 0/1 on clean/failing runs, echoes the seed, and reproduces a
// run when the seed is passed back. The generated tests import
// "lakatos/runtime" via the package self-reference, so these must run inside
// the repo tree (a gitignored scratch dir under .lakatos/), unlike the
// os.tmpdir()-based suites above.
describe("cli refute command (README usage claims)", () => {
  const workDir = path.join(repoRoot, ".lakatos", "clitest");

  beforeAll(() => {
    seedRefuteProject(workDir);
    process.chdir(workDir);
  });
  afterAll(() => {
    process.chdir(repoRoot);
    fs.rmSync(workDir, { recursive: true, force: true });
  });
  // Each test starts from a clean set of run directories; the tests that
  // exercise stale mirrors create their own staleness within the body.
  beforeEach(() => clearRunDirs(workDir));

  it(
    "refute still evaluates sound annotations beside InputError entries",
    { timeout: 60000 },
    async () => {
      const { code, stdout } = await runMain(["refute", "inputerr/mixed.ts"]);
      expect(code).toBe(2);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      const byProperty = Object.fromEntries(
        env.annotations.map((a: { property: string; szs: string }) => [
          a.property,
          a.szs,
        ]),
      );
      expect(byProperty).toEqual({ p: "InputError", q: "Theorem" });
      expect(env.generated).toBe(1);
    },
  );

  it(
    "refute falsifies a guarded property that 100 runs would pass",
    { timeout: 60000 },
    async () => {
      const { code, stdout } = await runMain([
        "refute",
        "--seed",
        "2",
        "guarded/conv.ts",
      ]);
      expect(code).toBe(1);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env.annotations).toHaveLength(1);
      expect(env.annotations[0]).toMatchObject({
        property: "naiveMonotone",
        szs: "CounterSatisfiable",
        kind: "falsified",
      });
    },
  );

  it(
    "refute runs an @ensures from every stacked JSDoc block",
    { timeout: 60000 },
    async () => {
      const { code, stdout } = await runMain(["refute", "stacked/keep.ts"]);
      expect(code).toBe(1);
      const env = JSON.parse(stdout[0]!);
      expectValidEnvelope(env);
      expect(env).toMatchObject({ generated: 2, passed: 1, failed: 1 });
      const byProperty = Object.fromEntries(
        env.annotations.map((a: { property: string; szs: string }) => [
          a.property,
          a.szs,
        ]),
      );
      expect(byProperty).toEqual({
        tooBig: "CounterSatisfiable",
        atLeastOne: "Theorem",
      });
    },
  );

  it(
    "refute runs an @ensures attached to a getter under Class#getter",
    { timeout: 60000 },
    async () => {
      const { code, stdout } = await runMain(["refute", "klass/box.ts"]);
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
    async () => {
      const { code, stdout } = await runMain(["refute", "good.ts"]);
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
    async () => {
      const { code, stdout } = await runMain(["refute", "bad.ts"]);
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
    async () => {
      const { code, stdout } = await runMain([
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
});
