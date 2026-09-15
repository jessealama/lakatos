import { describe, it, expect, afterAll, beforeAll, beforeEach } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import { clearRunDirs, seedRefuteProject } from "./helpers/refute-project.js";

const repoRoot = process.cwd();

// What an InputError does to the rest of a run: the sound annotations
// beside it still run, and its exit code outranks a refutation's. The
// generated tests import "lakatos/runtime" via the package self-reference,
// so these must run inside the repo tree, in a scratch directory of this
// file's own.
describe("cli refute input errors", () => {
  const workDir = path.join(repoRoot, ".lakatos", "clitest-inputerr");

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
