import { spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import * as path from 'node:path';
import { fileURLToPath } from 'node:url';

/** One #thales_prove verdict line: the contract printed by ThalesDsl. */
export interface LeanVerdict {
  identity: [string, string, string];
  szs: string;
  reason: string;
}

export type LeanRunResult =
  | { kind: 'completed'; verdicts: LeanVerdict[] }
  | { kind: 'no-project'; message: string }
  | { kind: 'failed'; stdout: string; stderr: string }
  | { kind: 'bad-verdicts'; messages: string[] };

const LEAN_TIMEOUT_MS = 300_000;
const BUILD_TIMEOUT_MS = 600_000;

/** Locate the ThalesDsl lake project: walk up from this module looking for
 * a lakefile here or under engines/thales — covers the source tree, the
 * compiled dist/ tree, and (by failing) installs without the Lean engine. */
export function findEngineRoot(
  from: string = fileURLToPath(import.meta.url),
): string | undefined {
  let dir = path.dirname(from);
  for (;;) {
    for (const c of [dir, path.join(dir, 'engines', 'thales')]) {
      if (existsSync(path.join(c, 'lakefile.lean'))) return c;
    }
    const parent = path.dirname(dir);
    if (parent === dir) return undefined;
    dir = parent;
  }
}

/** What runLean needs back from a spawn; a subset of spawnSync's return. */
interface SpawnOutcome {
  status: number | null;
  stdout: string | null;
  stderr: string | null;
  error?: Error;
}

type Spawn = (
  cmd: string,
  args: string[],
  opts: { cwd: string; encoding: 'utf8'; timeout: number },
) => SpawnOutcome;

function isVerdict(v: unknown): v is LeanVerdict {
  if (typeof v !== 'object' || v === null) return false;
  const o = v as Record<string, unknown>;
  return (
    Array.isArray(o.identity) &&
    o.identity.length === 3 &&
    o.identity.every((s) => typeof s === 'string') &&
    typeof o.szs === 'string' &&
    typeof o.reason === 'string'
  );
}

function parseVerdicts(
  stdout: string,
):
  | { kind: 'completed'; verdicts: LeanVerdict[] }
  | { kind: 'bad-verdicts'; messages: string[] } {
  const verdicts: LeanVerdict[] = [];
  const messages: string[] = [];
  for (const line of stdout.split('\n')) {
    if (line.trim() === '') continue;
    let v: unknown;
    try {
      v = JSON.parse(line);
    } catch {
      messages.push(`unparseable verdict line: ${line}`);
      continue;
    }
    if (!isVerdict(v)) {
      messages.push(`malformed verdict line: ${line}`);
      continue;
    }
    verdicts.push(v);
  }
  if (messages.length > 0) return { kind: 'bad-verdicts', messages };
  return { kind: 'completed', verdicts };
}

function isEnoent(e: Error | undefined): boolean {
  return e !== undefined && (e as NodeJS.ErrnoException).code === 'ENOENT';
}

function failed(r: SpawnOutcome): LeanRunResult {
  return {
    kind: 'failed',
    stdout: r.stdout ?? '',
    stderr: (r.stderr ?? '') + (r.error ? `${String(r.error)}\n` : ''),
  };
}

/**
 * Run `lake env lean` over each artifact and collect the JSON verdict
 * lines. `engineRoot` is the caller's `findEngineRoot()` result — absent
 * means this installation has no Lean engine. `lake build` runs first:
 * the DSL library must be compiled for the pinned toolchain, and a cached
 * build is a fast no-op.
 */
export function runLean(
  leanFiles: string[],
  engineRoot: string | undefined,
  spawn: Spawn = spawnSync,
): LeanRunResult {
  if (engineRoot === undefined) {
    return {
      kind: 'no-project',
      message:
        'the Lean proof engine is not part of this installation; run prove from a lakatos checkout',
    };
  }
  const opts = { cwd: engineRoot, encoding: 'utf8' } as const;
  const build = spawn('lake', ['build'], {
    ...opts,
    timeout: BUILD_TIMEOUT_MS,
  });
  if (isEnoent(build.error)) {
    return {
      kind: 'no-project',
      message:
        'lake was not found on PATH; install the Lean toolchain via elan (https://leanprover-community.github.io/get_started/) and re-run',
    };
  }
  if (build.error !== undefined || build.status !== 0) return failed(build);
  const verdicts: LeanVerdict[] = [];
  for (const file of leanFiles) {
    const run = spawn('lake', ['env', 'lean', path.resolve(file)], {
      ...opts,
      timeout: LEAN_TIMEOUT_MS,
    });
    if (run.error !== undefined || run.status !== 0) return failed(run);
    const parsed = parseVerdicts(run.stdout ?? '');
    if (parsed.kind === 'bad-verdicts') return parsed;
    verdicts.push(...parsed.verdicts);
  }
  return { kind: 'completed', verdicts };
}
