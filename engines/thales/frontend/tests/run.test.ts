import { afterEach, describe, expect, test, vi } from 'vitest';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { findEngineRoot, runEmission, runLean } from '../src/run.js';

type SpawnCall = { cmd: string; args: string[]; cwd: string };

/** A canned spawnSync: one scripted result per call, in order (the last
 * result repeats if calls overrun). Records every call for assertions. */
function fakeSpawn(
  results: Array<
    Partial<{
      status: number | null;
      signal: NodeJS.Signals;
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
      signal: r.signal ?? null,
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

  test('an interrupted build stops the run before any artifact', () => {
    const { spawn, calls } = fakeSpawn([
      { status: null, signal: 'SIGINT' },
      { status: 0, stdout: verdictLine('f', 'Theorem') },
    ]);
    const res = runLean(['a.lean'], '/engine', spawn);
    expect(res).toEqual({ kind: 'interrupted', signal: 'SIGINT' });
    expect(calls).toHaveLength(1);
  });

  test('an interrupted artifact stops the run: later files are not started', () => {
    const { spawn, calls } = fakeSpawn([
      { status: 0 }, // lake build
      { status: 0, stdout: verdictLine('f', 'Theorem') },
      { status: null, signal: 'SIGTERM' },
      { status: 0, stdout: verdictLine('h', 'Theorem') },
    ]);
    const res = runLean(['a.lean', 'b.lean', 'c.lean'], '/engine', spawn);
    // Verdicts a completed artifact already reported go down with the run:
    // the CLI reports every annotation it planned to attempt as User.
    expect(res).toEqual({ kind: 'interrupted', signal: 'SIGTERM' });
    expect(calls.map((c) => c.args.at(-1))).toEqual([
      'build',
      path.resolve('a.lean'),
      path.resolve('b.lean'),
    ]);
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
      // A status off the prove contract — invented, or refute's alone.
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"Proven","reason":"r"}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"InputError","reason":"r"}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"GaveUp","reason":""}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"Theorem","reason":"r","axioms":"Lean.ofReduceBool"}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"Theorem","reason":"r","axioms":[1]}',
      'thales-verdict:{"identity":["f.ts","f","p"],"szs":"Theorem","reason":"r","axioms":[""]}',
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

  test('a Theorem verdict keeps the axioms its proof rests on', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        {
          status: 0,
          stdout:
            'thales-verdict:{"identity":["t.ts","f","p"],"szs":"Theorem","reason":"r","axioms":["Lean.ofReduceBool"]}\n',
        },
      ]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'completed',
      verdicts: [
        {
          identity: ['t.ts', 'f', 'p'],
          szs: 'Theorem',
          axioms: ['Lean.ofReduceBool'],
        },
      ],
    });
  });

  test('a verdict must explain itself: an empty reason is malformed', () => {
    const res = runLean(
      ['a.lean'],
      '/engine',
      fakeSpawn([
        { status: 0 },
        {
          status: 0,
          stdout:
            'thales-verdict:{"identity":["t.ts","f","p"],"szs":"GaveUp","reason":""}\n',
        },
      ]).spawn,
    );
    expect(res).toMatchObject({
      kind: 'completed',
      verdicts: [],
      failures: [
        {
          file: 'a.lean',
          messages: [expect.stringContaining('malformed verdict line')],
        },
      ],
    });
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

  // stubEnv restores whatever the ambient environment held, so a value
  // exported outside the suite survives these tests.
  afterEach(() => {
    vi.unstubAllEnvs();
  });

  test('forwards LAKATOS_PROVE_HEARTBEATS to lean as a weak option', () => {
    const { spawn, calls } = fakeSpawn([{ status: 0 }, { status: 0 }]);
    vi.stubEnv('LAKATOS_PROVE_HEARTBEATS', '7');
    runLean(['a.lean'], '/engine', spawn);
    const leanCall = calls.find((c) => c.args[0] === 'env');
    expect(leanCall?.args).toContain('-Dweak.thales.heartbeats=7');
  });

  test.each([
    ['non-numeric', 'lots'],
    // 0 reaches Lean as maxHeartbeats 0, which means unlimited — the
    // opposite of the smallest budget someone setting it would expect.
    ['zero', '0'],
    ['zero-padded', '000'],
  ])('ignores a %s LAKATOS_PROVE_HEARTBEATS', (_label, value) => {
    const { spawn, calls } = fakeSpawn([{ status: 0 }, { status: 0 }]);
    vi.stubEnv('LAKATOS_PROVE_HEARTBEATS', value);
    runLean(['a.lean'], '/engine', spawn);
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

describe('runEmission', () => {
  const JOBS = [
    { jsonFile: 'a.json', leanFile: 'a.lean' },
    { jsonFile: 'b.json', leanFile: 'b.lean' },
  ];
  const EMIT_BIN = path.join('/engine', '.lake', 'build', 'bin', 'thales-emit');

  test('builds, emits each job, then runs each artifact', () => {
    const { spawn, calls } = fakeSpawn([
      { status: 0 }, // lake build
      { status: 0 }, // lake build thales-emit
      { status: 0 }, // emit a
      { status: 0 }, // emit b
      { status: 0, stdout: verdictLine('f', 'Theorem') },
      { status: 0, stdout: verdictLine('g', 'GaveUp') },
    ]);
    const res = runEmission(JOBS, '/engine', spawn);
    expect(res).toEqual({
      kind: 'completed',
      verdicts: [
        { identity: ['t.ts', 'f', 'p'], szs: 'Theorem', reason: 'r' },
        { identity: ['t.ts', 'g', 'p'], szs: 'GaveUp', reason: 'r' },
      ],
      failures: [],
      diagnostics: [],
    });
    expect(calls.map((c) => c.args.slice(0, 2))).toEqual([
      ['build'],
      ['build', 'thales-emit'],
      ['env', EMIT_BIN],
      ['env', EMIT_BIN],
      ['env', 'lean'],
      ['env', 'lean'],
    ]);
    expect(calls[2]!.args).toEqual(['env', EMIT_BIN, 'a.json', 'a.lean']);
    expect(calls.every((c) => c.cmd === 'lake' && c.cwd === '/engine')).toBe(
      true,
    );
  });

  test('an emit failure degrades only its own file; siblings still run', () => {
    const { spawn, calls } = fakeSpawn([
      { status: 0 },
      { status: 0 },
      { status: 1, stderr: 'boom' }, // emit a fails
      { status: 0 }, // emit b
      { status: 0, stdout: verdictLine('g', 'Theorem') }, // lean b
    ]);
    const res = runEmission(JOBS, '/engine', spawn);
    expect(res.kind).toBe('completed');
    if (res.kind !== 'completed') return;
    expect(res.failures).toHaveLength(1);
    expect(res.failures[0]!.file).toBe('a.lean');
    expect(res.failures[0]!.messages.join('\n')).toContain('boom');
    expect(res.verdicts).toHaveLength(1);
    // Only b's artifact reached the lean pass.
    expect(calls.filter((c) => c.args[1] === 'lean')).toHaveLength(1);
  });

  test("a spawn error during an emit carries the error's message into the failure", () => {
    const { spawn } = fakeSpawn([
      { status: 0 },
      { status: 0 },
      { status: 1, error: new Error('spawn thales-emit blew up') },
      { status: 0 },
      { status: 0, stdout: verdictLine('g', 'Theorem') },
    ]);
    const res = runEmission(JOBS, '/engine', spawn);
    expect(res.kind).toBe('completed');
    if (res.kind !== 'completed') return;
    expect(res.failures[0]!.file).toBe('a.lean');
    expect(res.failures[0]!.messages.join('\n')).toContain(
      'spawn thales-emit blew up',
    );
    expect(res.verdicts).toHaveLength(1);
  });

  test('an interrupt during the lean pass after the emits stops the run', () => {
    const { spawn } = fakeSpawn([
      { status: 0 }, // lake build
      { status: 0 }, // lake build thales-emit
      { status: 0 }, // emit a
      { status: 0 }, // emit b
      { status: 0, signal: 'SIGTERM' }, // lean a killed
    ]);
    const res = runEmission(JOBS, '/engine', spawn);
    expect(res).toEqual({ kind: 'interrupted', signal: 'SIGTERM' });
  });

  test('a thales-emit build failure fails the run', () => {
    const res = runEmission(
      JOBS,
      '/engine',
      fakeSpawn([{ status: 0 }, { status: 1, stderr: 'nope' }]).spawn,
    );
    expect(res.kind).toBe('failed');
  });

  test('an interrupt during an emit stops the run there', () => {
    const { spawn, calls } = fakeSpawn([
      { status: 0 },
      { status: 0 },
      { status: null, signal: 'SIGINT' },
    ]);
    const res = runEmission(JOBS, '/engine', spawn);
    expect(res).toEqual({ kind: 'interrupted', signal: 'SIGINT' });
    expect(calls).toHaveLength(3);
  });

  test('missing engine root is no-project', () => {
    expect(runEmission(JOBS, undefined, fakeSpawn([]).spawn).kind).toBe(
      'no-project',
    );
  });
});
