import { describe, it, expect, afterAll, beforeAll, beforeEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain } from "./helpers/cli.js";
import { clearRunDirs, seedRefuteProject } from "./helpers/refute-project.js";

const repoRoot = process.cwd();

// README usage claims about the seed: `lakatos refute` echoes the seed it
// used, and passing that seed back reproduces the run. The generated tests
// import "lakatos/runtime" via the package self-reference, so these must
// run inside the repo tree (a gitignored scratch dir under .lakatos/), and
// the directory is this file's own so a sibling suite's runs never appear
// beside these.
describe("cli refute seeds", () => {
  const workDir = path.join(repoRoot, ".lakatos", "clitest-seeds");

  beforeAll(() => {
    seedRefuteProject(workDir);
    process.chdir(workDir);
  });
  afterAll(() => {
    process.chdir(repoRoot);
    fs.rmSync(workDir, { recursive: true, force: true });
  });
  beforeEach(() => clearRunDirs(workDir));

  it(
    "refute --seed echoes the given seed in the envelope",
    { timeout: 60000 },
    async () => {
      const { code, stdout } = await runMain([
        "refute",
        "--seed",
        "123",
        "good.ts",
      ]);
      expect(code).toBe(0);
      expect(JSON.parse(stdout[0]!).seed).toBe(123);
    },
  );

  it(
    "passing a prior run's seed back reproduces that run",
    { timeout: 120000 },
    async () => {
      const first = JSON.parse(
        (await runMain(["refute", "bad.ts"])).stdout[0]!,
      );
      // Two degenerate runs would agree; pin that the baseline refuted before
      // comparing, so a degenerate baseline names itself instead of reading
      // like a seed bug.
      expect(first.annotations).toMatchObject([
        { szs: "CounterSatisfiable", kind: "falsified" },
      ]);
      clearRunDirs(workDir);
      const second = JSON.parse(
        (await runMain(["refute", "--seed", String(first.seed), "bad.ts"]))
          .stdout[0]!,
      );
      expect(second.seed).toBe(first.seed);
      expect(second.annotations).toEqual(first.annotations);
      expect(second.passed).toBe(first.passed);
      expect(second.failed).toBe(first.failed);
    },
  );
});
