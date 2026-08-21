import { execFileSync } from "node:child_process";
import { realpathSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

const repoRoot = path.dirname(path.dirname(fileURLToPath(import.meta.url)));

/**
 * One tsc for the whole run. Several suites exercise the *built* CLI in
 * dist/, and test files run in parallel: building per file would have two
 * tsc processes truncating and rewriting the same output while a third
 * suite reads or spawns it.
 *
 * refute spawns its own vitest on generated tests, and one whose cwd is
 * inside the repo tree inherits this config — that run must not rebuild
 * dist/ underneath the parent's suites, so it is skipped by cwd.
 */
export default function setup(): void {
  if (realpathSync(process.cwd()) !== realpathSync(repoRoot)) return;
  execFileSync("npx", ["tsc", "-p", "tsconfig.json"], {
    cwd: repoRoot,
    stdio: "inherit",
  });
}
