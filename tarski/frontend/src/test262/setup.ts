// Provisioning test262 at a pinned commit.
//
// Never a submodule: the epic says so, and a submodule would put the
// suite's history in every clone of this repository whether or not anyone
// runs the evaluator. What this does instead is what `actions/checkout`
// does — `git init`, a remote, and a depth-1 fetch of one SHA, which
// GitHub serves for any reachable commit. The clone is gitignored, so it
// is a build artifact like `.lake/`.

import { execFileSync as nodeExecFileSync } from "node:child_process";
import { existsSync, mkdirSync } from "node:fs";
import path from "node:path";

/** The commit the suite is read at, and where to get it. */
export interface Pin {
  repository: string;
  commit: string;
}

/** `execFileSync`, narrowed to what this uses. */
export type Exec = (
  command: string,
  args: readonly string[],
  options: { cwd?: string; encoding: "utf8"; stdio: "pipe" },
) => string;

const run = (exec: Exec, args: readonly string[], cwd?: string): string =>
  exec("git", args, {
    ...(cwd === undefined ? {} : { cwd }),
    encoding: "utf8",
    stdio: "pipe",
  });

/** The commit checked out in `dir`, or `undefined` when there is no repository. */
function headOf(dir: string, exec: Exec): string | undefined {
  if (!existsSync(path.join(dir, ".git"))) return undefined;
  try {
    return run(exec, ["-C", dir, "rev-parse", "HEAD"], undefined).trim();
  } catch {
    // An interrupted fetch leaves a repository with no HEAD. Re-fetching
    // is the cheapest way back.
    return undefined;
  }
}

/**
 * Put `dir` at the pinned commit, fetching it if it is not there already.
 * A checkout already at the pin is left alone, which is what makes this
 * safe to run before every slice and cheap in a cached CI job.
 */
export function setupTest262(
  dir: string,
  pin: Pin,
  log: (line: string) => void,
  exec: Exec = nodeExecFileSync as Exec,
): void {
  if (headOf(dir, exec) === pin.commit) {
    log(`test262 already at ${pin.commit}`);
    return;
  }
  mkdirSync(dir, { recursive: true });
  if (!existsSync(path.join(dir, ".git"))) run(exec, ["init", "--quiet"], dir);
  try {
    run(exec, ["remote", "add", "origin", pin.repository], dir);
  } catch {
    // Already there, pointing somewhere that may no longer be the pin's.
    run(exec, ["remote", "set-url", "origin", pin.repository], dir);
  }
  log(`fetching ${pin.commit} from ${pin.repository}`);
  run(exec, ["fetch", "--depth", "1", "origin", pin.commit], dir);
  run(exec, ["checkout", "--quiet", "FETCH_HEAD"], dir);
  log(`test262 at ${pin.commit} in ${dir}`);
}
