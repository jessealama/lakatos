// The evaluator binary as a dependency: locate it, build it, run one
// document through it.
//
// This is `lakatos exe`'s side of the seam, and it lives in tarski's own
// tree rather than beside thales's `run.ts` because the layering forbids
// tarski from importing an engine. The two are deliberately alike — one
// `lake build` under a timeout, ENOENT read as a missing toolchain, a
// nonzero status carried out with both streams — and thales's copy is the
// model, not a module to share.

import { spawnSync } from "node:child_process";
import { defaultBinary } from "./test262/paths.js";

/** The budget one `lake build tarski` gets; thales's is the same. */
export const BUILD_TIMEOUT_MS = 600_000;

/** What this module needs back from a spawn; a subset of spawnSync's. */
export interface SpawnOutcome {
  status: number | null;
  signal?: NodeJS.Signals | null;
  stdout: string | null;
  stderr: string | null;
  error?: Error;
}

export type Spawn = (
  cmd: string,
  args: string[],
  opts: {
    cwd?: string;
    encoding: "utf8";
    timeout?: number;
    maxBuffer?: number;
  },
) => SpawnOutcome;

export type BinaryResult =
  | { kind: "ready"; binary: string }
  /** There is no evaluator to run here: no lake package, or no lake. */
  | { kind: "no-project"; message: string }
  /** The build itself failed; both streams are the user's diagnosis. */
  | { kind: "failed"; stdout: string; stderr: string };

function isEnoent(e: Error | undefined): boolean {
  return e !== undefined && (e as NodeJS.ErrnoException).code === "ENOENT";
}

/**
 * The binary, built. The build is repeated on every invocation for the
 * reason `prove` rebuilds thales on every invocation: a cached lake build
 * is a fast no-op, and a binary that was built from some other checkout
 * would evaluate some other semantics than the one this tree defines.
 *
 * The caller resolves `root` — `findTarskiRoot()` is what every real one
 * passes — as `runEmission` does with `findEngineRoot`, and for the same
 * reason: a default parameter is chosen whenever the argument is
 * `undefined`, which is exactly the case this function has to answer for.
 */
export function ensureBinary(
  root: string | undefined,
  spawn: Spawn = spawnSync,
): BinaryResult {
  if (root === undefined) {
    return {
      kind: "no-project",
      message:
        "the tarski evaluator is not part of this installation; run exe from a lakatos checkout",
    };
  }
  const build = spawn("lake", ["build", "tarski"], {
    cwd: root,
    encoding: "utf8",
    timeout: BUILD_TIMEOUT_MS,
  });
  if (isEnoent(build.error)) {
    return {
      kind: "no-project",
      message:
        "lake was not found on PATH; install the Lean toolchain via elan (https://leanprover-community.github.io/get_started/) and re-run",
    };
  }
  if (build.error !== undefined || build.status !== 0) {
    return {
      kind: "failed",
      // A spawn that never started answers with both streams null, so
      // neither is assumed.
      stdout: build.stdout ?? "",
      stderr:
        (build.stderr ?? "") + (build.error ? `${String(build.error)}\n` : ""),
    };
  }
  return { kind: "ready", binary: defaultBinary(root) };
}

/**
 * One document through `tarski exec`. There is no timeout: a program that
 * diverges hangs exactly as it would under `node`, and the Ctrl-C that
 * ends the user's wait ends both processes. The buffer is large because
 * the program's whole stdout arrives at once.
 */
export function runDocument(
  binary: string,
  documentPath: string,
  spawn: Spawn = spawnSync,
): SpawnOutcome {
  return spawn(binary, ["exec", documentPath], {
    encoding: "utf8",
    maxBuffer: 256 * 1024 * 1024,
  });
}
