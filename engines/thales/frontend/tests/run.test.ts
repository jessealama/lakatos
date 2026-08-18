import { describe, expect, test } from 'vitest';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { findEngineRoot, runLean } from '../src/run.js';

type SpawnCall = { cmd: string; args: string[]; cwd: string };

/** A canned spawnSync: one scripted result per call, in order (the last
 * result repeats if calls overrun). Records every call for assertions. */
function fakeSpawn(
  results: Array<
    Partial<{
      status: number | null;
      stdout: string;
      stderr: string;
      error: Error;
    }>
  >,
  calls: SpawnCall[] = [],
) {
  let i = 0;
  const spawn = ((cmd: string, args: string[], opts: { cwd?: string }) => {
    calls.push({ cmd, args, cwd: String(opts.cwd) });
    const r = results[Math.min(i++, results.length - 1)]!;
    return {
      status: r.status ?? 0,
      stdout: r.stdout ?? '',
      stderr: r.stderr ?? '',
      error: r.error,
    };
  }) as never;
  return { spawn, calls };
}

const verdictLine = (fn: string, szs: string) =>
  JSON.stringify({ identity: ['t.ts', fn, 'p'], szs, reason: 'r' }) + '\n';

describe('runLean', () => {
  test('collects verdict lines across files in order', () => {
    const { spawn, calls } = fakeSpawn([
      { status: 0 }, // lake build
      { status: 0, stdout: verdictLine('f', 'Theorem') },
      {
        status: 0,
        stdout: verdictLine('g', 'GaveUp') + verdictLine('h', 'Inappropriate'),
      },
    ]);
    const res = runLean(['a.lean', 'b.lean'], '/engine', spawn);
    expect(res).toEqual({
      kind: 'completed',
      verdicts: [
        { identity: ['t.ts', 'f', 'p'], szs: 'Theorem', reason: 'r' },
        { identity: ['t.ts', 'g', 'p'], szs: 'GaveUp', reason: 'r' },
        { identity: ['t.ts', 'h', 'p'], szs: 'Inappropriate', reason: 'r' },
      ],
    });
    expect(calls.map((c) => c.args[0])).toEqual(['build', 'env', 'env']);
    expect(calls.every((c) => c.cmd === 'lake' && c.cwd === '/engine')).toBe(
      true,
    );
  });

  test('missing engine root is no-project', () => {
    const res = runLean(['a.lean'], undefined, fakeSpawn([]).spawn);
    expect(res.kind).toBe('no-project');
  });

  test('lake absent from PATH is no-project with install guidance', () => {
    const enoent = Object.assign(new Error('spawn lake ENOENT'), {
      code: 'ENOENT',
    });
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([{ error: enoent, status: null }]).spawn,
    );
    expect(res.kind).toBe('no-project');
    expect((res as { message: string }).message).toContain('elan');
  });

  test('a failing lake build is failed with its output', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([{ status: 1, stderr: 'boom' }]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'failed',
      stderr: expect.stringContaining('boom'),
    });
  });

  test('a failing lean run is failed with its output', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([{ status: 0 }, { status: 1, stderr: 'elab error' }]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'failed',
      stderr: expect.stringContaining('elab error'),
    });
  });

  test('a spawn-level error on a lean run is failed', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        { status: null, error: new Error('ETIMEDOUT') },
      ]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'failed',
      stderr: expect.stringContaining('ETIMEDOUT'),
    });
  });

  test('unparseable or malformed stdout lines are bad-verdicts', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        { status: 0, stdout: 'not json\n{"identity":["a"],"szs":1}\n' },
      ]).spawn,
    );
    expect(res.kind).toBe('bad-verdicts');
    expect((res as { messages: string[] }).messages).toHaveLength(2);
  });
});

describe('findEngineRoot', () => {
  test('finds a lakefile at engines/thales relative to an enclosing directory', () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'thales-root-'));
    try {
      fs.mkdirSync(path.join(dir, 'engines', 'thales'), { recursive: true });
      fs.writeFileSync(
        path.join(dir, 'engines', 'thales', 'lakefile.lean'),
        '',
      );
      const from = path.join(dir, 'dist', 'src', 'cli.js');
      expect(findEngineRoot(from)).toBe(path.join(dir, 'engines', 'thales'));
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  });

  test('resolves the real repository engine root by default', () => {
    expect(findEngineRoot()?.endsWith(path.join('engines', 'thales'))).toBe(
      true,
    );
  });
});
