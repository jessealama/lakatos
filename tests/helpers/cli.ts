import { beforeAll, afterAll, expect, vi } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { main } from "../../src/cli.js";
import { expectValidEnvelope } from "./envelope-schema.js";
import type { Envelope } from "../../src/envelope.js";
import {
  BUILD_TIMEOUT_MS,
  LEAN_TIMEOUT_MS,
} from "../../engines/thales/frontend/src/run.js";

export interface MainRun {
  code: number;
  stdout: string[];
  stderr: string[];
}

/**
 * Run the CLI's main() with both console streams captured, so tests can
 * assert on diagnostics regardless of which stream they land on.
 */
export function runMain(argv: string[]): MainRun {
  const stdout: string[] = [];
  const stderr: string[] = [];
  const logSpy = vi.spyOn(console, "log").mockImplementation((s) => {
    stdout.push(String(s));
  });
  const errSpy = vi.spyOn(console, "error").mockImplementation((s) => {
    stderr.push(String(s));
  });
  try {
    return { code: main(argv), stdout, stderr };
  } finally {
    logSpy.mockRestore();
    errSpy.mockRestore();
  }
}

/**
 * Captured stderr without the type-check gate's skip warning, which every
 * tsconfig-less fixture provokes and which no test about diagnostics means.
 */
export function withoutSkipWarning(stderr: string[]): string[] {
  return stderr.filter((l) => !l.startsWith("lakatos: no tsconfig.json;"));
}

/**
 * The run directory the CLI announced on stderr. Tests read it the way a
 * user does rather than recomputing it from the envelope's startedAt: a run
 * whose name was taken steps to the next free one, so the two can differ.
 */
export function announcedRunDir(stderr: string[]): string {
  const m = /into (.+)[/\\](?:pabst|thales)\/$/m.exec(stderr.join("\n"));
  if (m === null)
    throw new Error(`no run directory announced in: ${stderr.join("\n")}`);
  return m[1]!;
}

/**
 * Run main() and unwrap the single-envelope contract: the expected exit
 * code (0 unless the run is meant to find counterexamples), exactly one
 * stdout line, and that line a schema-valid envelope.
 */
export function runForEnvelope(argv: string[], expectedCode = 0): Envelope {
  const run = runMain(argv);
  expect(run.code, run.stderr.join("\n")).toBe(expectedCode);
  expect(run.stdout).toHaveLength(1);
  const env = JSON.parse(run.stdout[0]!) as Envelope;
  expectValidEnvelope(env);
  return env;
}

/**
 * Test-timeout ceiling for one `prove` run over `fileCount` artifacts: the
 * pipeline's own containment budget (one build, one Lean run per file) plus
 * slack, so a contained-but-slow run gets to report which file failed
 * instead of being killed by a bare vitest timeout.
 */
export function proveTimeoutMs(fileCount: number): number {
  return BUILD_TIMEOUT_MS + fileCount * LEAN_TIMEOUT_MS + 60_000;
}

/**
 * Like useTempProject, but the directory lives inside the repo tree:
 * refute's generated tests import "lakatos/runtime" via the package
 * self-reference, so suites that run refute cannot work under os.tmpdir().
 * `populate` writes the project's files before the chdir.
 */
export function useRepoScratchDir(
  workDir: string,
  populate: (dir: string) => void,
): void {
  const prevCwd = process.cwd();
  beforeAll(() => {
    fs.rmSync(workDir, { recursive: true, force: true });
    fs.mkdirSync(workDir, { recursive: true });
    populate(workDir);
    process.chdir(workDir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(workDir, { recursive: true, force: true });
  });
}

/**
 * Create a temp directory populated with `files` and chdir into it for the
 * duration of the enclosing describe block (registers beforeAll/afterAll).
 * Returns the directory path.
 */
export function useTempProject(
  prefix: string,
  files: Record<string, string>,
): string {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), prefix));
  const prevCwd = process.cwd();
  beforeAll(() => {
    for (const [name, text] of Object.entries(files)) {
      const dest = path.join(dir, name);
      fs.mkdirSync(path.dirname(dest), { recursive: true });
      fs.writeFileSync(dest, text, "utf8");
    }
    process.chdir(dir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(dir, { recursive: true, force: true });
  });
  return dir;
}
