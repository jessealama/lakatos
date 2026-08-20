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
    // Omitted streams become null, as spawnSync yields on spawn failure.
    return {
      status: r.status ?? 0,
      stdout: r.stdout ?? null,
      stderr: r.stderr ?? null,
      error: r.error,
    };
  }) as never;
  return { spawn, calls };
}

const verdictLine = (fn: string, szs: string) =>
  'thales-verdict:' +
  JSON.stringify({ identity: ['t.ts', fn, 'p'], szs, reason: 'r' }) +
  '\n';

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
      failures: [],
      diagnostics: [],
    });
    expect(calls.map((c) => c.args[0])).toEqual(['build', 'env', 'env']);
    expect(calls.every((c) => c.cmd === 'lake' && c.cwd === '/engine')).toBe(
      true,
    );
  });

  test('a counterexample rides through, numbers and decimal strings alike', () => {
    const line =
      'thales-verdict:{"identity":["t.ts","f","p"],"szs":"CounterSatisfiable",' +
      '"reason":"r","counterexample":{"x":0,"y":"9007199254740992"}}\n';
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([{ status: 0 }, { status: 0, stdout: line }]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'completed',
      verdicts: [
        {
          identity: ['t.ts', 'f', 'p'],
          szs: 'CounterSatisfiable',
          reason: 'r',
          counterexample: { x: 0, y: '9007199254740992' },
        },
      ],
      failures: [],
    });
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

  test('a spawn-level error on lake build that is not ENOENT is failed', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([{ status: null, error: new Error('EACCES') }]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'failed',
      stderr: expect.stringContaining('EACCES'),
    });
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

  test('a failing lean run is contained: other files still report', () => {
    const res = runLean(
      ['a.lean', 'b.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        { status: 1, stderr: 'elab error' },
        { status: 0, stdout: verdictLine('g', 'Theorem') },
      ]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'completed',
      verdicts: [{ identity: ['t.ts', 'g', 'p'], szs: 'Theorem', reason: 'r' }],
      failures: [
        {
          file: 'a.lean',
          messages: expect.arrayContaining([
            expect.stringContaining('elab error'),
          ]),
        },
      ],
    });
  });

  test('a spawn-level error (timeout) on one file is contained', () => {
    const res = runLean(
      ['a.lean', 'b.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        { status: null, error: new Error('ETIMEDOUT') },
        { status: 0, stdout: verdictLine('g', 'GaveUp') },
      ]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'completed',
      failures: [
        {
          file: 'a.lean',
          messages: expect.arrayContaining([
            expect.stringContaining('ETIMEDOUT'),
          ]),
        },
      ],
    });
    expect((res as { verdicts: unknown[] }).verdicts).toHaveLength(1);
  });

  test('malformed framed lines fail only their own file', () => {
    const malformed = [
      'thales-verdict:not json',
      'thales-verdict:42',
      'thales-verdict:null',
      'thales-verdict:{"identity":["a"],"szs":1}',
      'thales-verdict:{"identity":[1,2,3],"szs":"Theorem","reason":"r"}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"Theorem"}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"CounterSatisfiable","reason":"r","counterexample":[]}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"CounterSatisfiable","reason":"r","counterexample":{"x":true}}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"CounterSatisfiable","reason":"r","counterexample":{"x":null}}',
    ];
    const res = runLean(
      ['a.lean', 'b.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        { status: 0, stdout: malformed.join('\n') + '\n' },
        { status: 0, stdout: verdictLine('g', 'Theorem') },
      ]).spawn,
    );
    expect(res).toMatchObject({ kind: 'completed' });
    const r = res as {
      verdicts: unknown[];
      failures: { file: string; messages: string[] }[];
    };
    expect(r.verdicts).toHaveLength(1);
    expect(r.failures).toHaveLength(1);
    expect(r.failures[0]!.messages).toHaveLength(malformed.length);
  });

  test('a healthy run with no stdout at all yields no verdicts', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([{ status: 0 }, { status: 0 }]).spawn,
    );
    expect(res).toEqual({
      kind: 'completed',
      verdicts: [],
      failures: [],
      diagnostics: [],
    });
  });

  test('forwards LAKATOS_PROVE_HEARTBEATS to lean as a weak option', () => {
    const { spawn, calls } = fakeSpawn([{ status: 0 }, { status: 0 }]);
    process.env.LAKATOS_PROVE_HEARTBEATS = '7';
    try {
      runLean(['a.lean'], '/engine', spawn);
    } finally {
      delete process.env.LAKATOS_PROVE_HEARTBEATS;
    }
    const leanCall = calls.find((c) => c.args[0] === 'env');
    expect(leanCall?.args).toContain('-Dweak.thales.heartbeats=7');
  });

  test('ignores a non-numeric LAKATOS_PROVE_HEARTBEATS', () => {
    const { spawn, calls } = fakeSpawn([{ status: 0 }, { status: 0 }]);
    process.env.LAKATOS_PROVE_HEARTBEATS = 'lots';
    try {
      runLean(['a.lean'], '/engine', spawn);
    } finally {
      delete process.env.LAKATOS_PROVE_HEARTBEATS;
    }
    expect(calls.flatMap((c) => c.args).join(' ')).not.toContain(
      'thales.heartbeats',
    );
  });

  test('unframed stdout lines are diagnostics, not failures', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        {
          status: 0,
          stdout: 'note: some linter chatter\n' + verdictLine('f', 'Theorem'),
        },
      ]).spawn,
    );
    expect(res).toEqual({
      kind: 'completed',
      verdicts: [{ identity: ['t.ts', 'f', 'p'], szs: 'Theorem', reason: 'r' }],
      failures: [],
      diagnostics: ['note: some linter chatter'],
    });
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

  test('is undefined when no lakefile exists anywhere up the tree', () => {
    expect(
      findEngineRoot(path.join(path.sep, 'no-such-lakatos-root', 'x.js')),
    ).toBeUndefined();
  });

  test('resolves the real repository engine root by default', () => {
    expect(findEngineRoot()?.endsWith(path.join('engines', 'thales'))).toBe(
      true,
    );
  });
});
