import { describe, it, expect, beforeAll, afterAll } from "vitest";
import { execFileSync, spawn } from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";

// The acceptance test for the interruption contract, with a real signal:
// the built CLI leads its own process group, so the SIGINT sent here is
// the one Ctrl-C sends at a terminal — it reaches the CLI and the vitest
// it spawned alike.
const repoRoot = process.cwd();
const cliJs = path.join(repoRoot, "dist", "src", "cli.js");
// Inside the repo tree: the generated tests resolve "lakatos/runtime" by
// package self-reference and the spawned vitest finds its binary by
// walking up node_modules, neither of which works from os.tmpdir().
const workDir = path.join(repoRoot, ".pabst", "interrupt-e2e");

/** The property under test drops this the first time it is evaluated,
 * so the signal can be sent while vitest is genuinely mid-run — the
 * shape a Ctrl-C actually takes — rather than during its startup. */
const MARKER = "running";

// Each generated run of this property burns real time, so the run is
// still going when the signal lands.
const SLOW = [
  'import { writeFileSync } from "node:fs";',
  "",
  "/** @ensures{pos} forall (n: int ∈ [0, 100]) { slow(n) >= 0 } */",
  "export function slow(n: number): number {",
  `  writeFileSync(${JSON.stringify(MARKER)}, "x");`,
  "  const until = Date.now() + 30;",
  "  while (Date.now() < until) {}",
  "  return n;",
  "}",
  "",
].join("\n");

async function waitFor(
  what: string,
  ready: () => boolean,
  timeoutMs = 30_000,
): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (!ready()) {
    if (Date.now() > deadline) throw new Error(`timed out waiting for ${what}`);
    await new Promise((r) => setTimeout(r, 100));
  }
}

describe("lakatos refute interrupted by a real SIGINT", () => {
  beforeAll(() => {
    execFileSync("npx", ["tsc", "-p", "tsconfig.json"], { cwd: repoRoot });
    fs.rmSync(workDir, { recursive: true, force: true });
    fs.mkdirSync(workDir, { recursive: true });
    fs.writeFileSync(path.join(workDir, "slow.ts"), SLOW, "utf8");
    // The spawned vitest inherits the nearest config walking up from its
    // cwd; pin an empty one so this run is not shaped by the repo's.
    fs.writeFileSync(
      path.join(workDir, "vitest.config.ts"),
      `import { defineConfig } from "vitest/config";\nexport default defineConfig({});\n`,
      "utf8",
    );
  }, 180_000);

  afterAll(() => {
    fs.rmSync(workDir, { recursive: true, force: true });
  });

  it("prints a User envelope on stdout and exits 2", async () => {
    const child = spawn(process.execPath, [cliJs, "refute", "slow.ts"], {
      cwd: workDir,
      detached: true,
    });
    let stdout = "";
    let stderr = "";
    child.stdout.setEncoding("utf8");
    child.stdout.on("data", (c: string) => (stdout += c));
    child.stderr.setEncoding("utf8");
    child.stderr.on("data", (c: string) => (stderr += c));
    const pid = child.pid!;
    const exited = new Promise<number | null>((resolve) =>
      child.on("close", resolve),
    );

    await waitFor("the property to start running under vitest", () =>
      fs.existsSync(path.join(workDir, MARKER)),
    );
    process.kill(-pid, "SIGINT");

    expect(await exited).toBe(2);
    expect(stderr).toContain("interrupted by SIGINT");
    const env = JSON.parse(stdout);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      {
        file: "slow.ts",
        function: "slow",
        property: "pos",
        szs: "User",
        reason: "the run was interrupted (SIGINT)",
      },
    ]);
    expect(env.passed).toBeUndefined();
    expect(env.failed).toBeUndefined();
  }, 180_000);
});
