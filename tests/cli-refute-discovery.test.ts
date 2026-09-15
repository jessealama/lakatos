import { describe, it, expect, afterAll, beforeAll, beforeEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { clearRunDirs, seedRefuteProject } from "./helpers/refute-project.js";

const repoRoot = process.cwd();

// Where refute finds an @ensures: in every stacked JSDoc block, and on a
// getter, reported under Class#getter. The generated tests import
// "lakatos/runtime" via the package self-reference, so these must run
// inside the repo tree, in a scratch directory of this file's own.
describe("cli refute annotation discovery", () => {
  const workDir = path.join(repoRoot, ".lakatos", "clitest-discovery");

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
});
