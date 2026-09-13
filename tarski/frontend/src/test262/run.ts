// Running one planned test against the `tarski` binary, and reading its
// exit code as an outcome.
//
// The binary's contract is `Tarski/Main.lean`'s header: 0 ran, 1 uncaught,
// 2 bad input, 3 unsupported, and a wall clock for divergence. Every
// outcome class below is one of those, plus the two the runner itself can
// produce — a timeout it imposed, and its own machinery failing.
//
// `classify` is separated from the spawn so that every arm is reachable
// from a hand-built value; `runOne` is the part that touches the disk.

import {
  spawnSync as nodeSpawnSync,
  type SpawnSyncReturns,
} from "node:child_process";
import { writeFileSync } from "node:fs";
import path from "node:path";
import { ParseError, parseScript } from "../estree.js";
import type { Plan } from "./plan.js";

/** What a test run came to. */
export type Outcome =
  | { class: "pass" }
  | { class: "fail"; detail: string }
  | { class: "unsupported"; kind: string }
  | { class: "timeout" }
  | { class: "harness-error"; detail: string };

/** The part of `spawnSync`'s answer this reads. */
export interface SpawnOutcome {
  status: number | null;
  signal: NodeJS.Signals | null;
  stderr: string;
  error?: Error & { code?: string };
}

/** The first line of a report, which is where the binary puts the summary. */
function firstLine(stderr: string): string {
  return stderr.split("\n")[0] ?? "";
}

/**
 * The class of an uncaught error, read off `Uncaught <Name>: <message>`.
 * `undefined` when the report carries no name: a thrown primitive prints
 * as itself, and an abrupt completion outside any loop prints
 * `Uncaught: …`.
 */
function thrownClass(stderr: string): string | undefined {
  return /^Uncaught ([A-Za-z_$][\w$]*)(?::|$)/.exec(firstLine(stderr))?.[1];
}

/** What the binary said was unsupported, or the whole line if it did not say. */
function unsupportedKind(stderr: string): string {
  const line = firstLine(stderr);
  const marker = line.indexOf("unsupported: ");
  return marker < 0 ? line : line.slice(marker + "unsupported: ".length);
}

/**
 * One spawn's answer as an outcome. `negative` is the class a
 * runtime-phase negative test must end with, and `undefined` for every
 * other test.
 */
export function classify(
  result: SpawnOutcome,
  negative: { type: string } | undefined,
): Outcome {
  // A killed process is the timeout the runner imposed: `spawnSync` kills
  // by signal and reports ETIMEDOUT beside it.
  if (result.signal !== null || result.error?.code === "ETIMEDOUT") {
    return { class: "timeout" };
  }
  if (result.error !== undefined) {
    return { class: "harness-error", detail: result.error.message };
  }
  if (result.status === 3)
    return { class: "unsupported", kind: unsupportedKind(result.stderr) };
  if (result.status === 0) {
    if (negative === undefined) return { class: "pass" };
    return {
      class: "fail",
      detail: `expected an uncaught ${negative.type}, the script completed`,
    };
  }
  if (result.status === 1) {
    const thrown = thrownClass(result.stderr);
    if (negative === undefined)
      return { class: "fail", detail: firstLine(result.stderr) };
    if (thrown === negative.type) return { class: "pass" };
    return {
      class: "fail",
      detail: `expected an uncaught ${negative.type}, got ${firstLine(result.stderr)}`,
    };
  }
  // Exit 2 is the binary refusing its input, and any other status is a
  // binary that is not the one this runner knows. Both are the runner's
  // own machinery, not the test's.
  return {
    class: "harness-error",
    detail: firstLine(result.stderr) || `exit ${result.status}`,
  };
}

/** `spawnSync`, narrowed to what `classify` reads. */
export type Spawn = (
  command: string,
  args: readonly string[],
  options: { encoding: "utf8"; timeout: number },
) => SpawnSyncReturns<string>;

/**
 * Parse one planned test, write the ESTree document into `scratch`, and
 * run the binary on it. A source that does not parse is the runner's own
 * machinery failing: the parse-phase negatives are skipped, so nothing
 * that reaches here is meant not to parse.
 */
export function runOne(
  plan: Extract<Plan, { kind: "run" }>,
  binary: string,
  timeoutMs: number,
  scratch: string,
  spawn: Spawn = nodeSpawnSync as Spawn,
): Outcome {
  let document: string;
  try {
    document = JSON.stringify(parseScript(plan.source, "test262"));
  } catch (e) {
    return { class: "harness-error", detail: (e as ParseError).message };
  }
  const file = path.join(scratch, "test.json");
  writeFileSync(file, document);
  const result = spawn(binary, ["run", file], {
    encoding: "utf8",
    timeout: timeoutMs,
  });
  return classify(
    {
      status: result.status,
      signal: result.signal,
      stderr: result.stderr ?? "",
      ...(result.error === undefined ? {} : { error: result.error }),
    },
    plan.negative,
  );
}
