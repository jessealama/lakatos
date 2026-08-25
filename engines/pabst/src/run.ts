import { spawnSync } from "node:child_process";
import { readFileSync, rmSync } from "node:fs";
import { interruptedBy, type InterruptSignal } from "../../../src/interrupt.js";
import type { FileResult, VitestJson } from "./vitest-json.js";

export type RunResult =
  | { kind: "completed"; json: VitestJson }
  | { kind: "no-results"; status: number; stdout: string; stderr: string }
  | { kind: "broken-run"; status: number; messages: string[] }
  | { kind: "interrupted"; signal: InterruptSignal };

/** What runTests needs back from a spawn; a subset of spawnSync's return. */
export interface SpawnOutcome {
  status: number | null;
  signal?: NodeJS.Signals | null;
  stdout: string | null;
  stderr: string | null;
  error?: Error;
}

type Spawn = (
  cmd: string,
  args: string[],
  opts: { encoding: "utf8" },
) => SpawnOutcome;

/**
 * Run vitest over `target` (the generated out-files of one invocation, or a
 * single file or directory) and return its parsed JSON results. When vitest
 * produces no parseable results file (e.g. it died on startup before its
 * reporter ran), the run yielded nothing trustworthy to report: instead,
 * return vitest's raw output and exit status so the caller can surface the
 * underlying error.
 */
export function runTests(
  target: string | string[],
  resultsFile: string,
  spawn: Spawn = spawnSync,
): RunResult {
  // A stale results file from a previous run must not be mistaken for this
  // run's output when vitest dies before writing one.
  try {
    rmSync(resultsFile, { force: true });
  } catch (e) {
    return {
      kind: "no-results",
      status: 1,
      stdout: "",
      stderr: `lakatos: cannot clear stale results file ${resultsFile}: ${e instanceof Error ? e.message : String(e)}\n`,
    };
  }
  const targets = Array.isArray(target) ? target : [target];
  const res = spawn(
    "npx",
    [
      "vitest",
      "run",
      ...targets,
      "--reporter=json",
      `--outputFile=${resultsFile}`,
    ],
    { encoding: "utf8" },
  );
  // A vitest killed by a termination signal took the whole run with it:
  // whatever it left on disk is partial, so the interruption is reported
  // before any results file is read.
  const signal = interruptedBy(res);
  if (signal !== undefined) return { kind: "interrupted", signal };
  let json;
  try {
    json = JSON.parse(readFileSync(resultsFile, "utf8"));
  } catch {
    return {
      kind: "no-results",
      status: res.status ?? 1,
      stdout: res.stdout ?? "",
      stderr: (res.stderr ?? "") + (res.error ? `${String(res.error)}\n` : ""),
    };
  }
  // An unhealthy run vitest couldn't attribute to any test (e.g. a test file
  // that failed to load) must not be reported as a trustworthy envelope. The
  // json reporter keeps the underlying errors in each file's `message`, not
  // on stdout/stderr.
  if (json.success === false && json.numFailedTests === 0) {
    const messages = ((json.testResults ?? []) as FileResult[]).flatMap((f) =>
      f.status === "failed" && f.message ? [f.message] : [],
    );
    return { kind: "broken-run", status: res.status || 1, messages };
  }
  return { kind: "completed", json };
}
