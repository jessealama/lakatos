import { afterAll, beforeAll, describe, expect, test } from 'vitest';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { LemmaError } from '../../../../lemma/src/index.js';
import { writeArtifacts } from '../src/artifacts.js';

// The out root is the caller's to choose; these tests pick an arbitrary one
// to keep the mirroring under test independent of what the CLI names it.
const OUT = 'out';

const ANNOTATED =
  '/** @ensures{q} forall (x: int ∈ [0, 5)) { f(x) === x } */\nexport function f(x: number): number { return x; }\n';

describe('writeArtifacts', () => {
  let dir: string;
  const prevCwd = process.cwd();
  beforeAll(() => {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), 'thales-artifacts-'));
    fs.mkdirSync(path.join(dir, 'sub'));
    fs.writeFileSync(path.join(dir, 'sub', 'a.ts'), ANNOTATED);
    fs.writeFileSync(path.join(dir, 'plain.ts'), 'export const x = 1;\n');
    fs.writeFileSync(path.join(dir, 'x.ts'), ANNOTATED);
    fs.writeFileSync(path.join(dir, 'x.tsx'), ANNOTATED);
    fs.writeFileSync(
      path.join(dir, 'huge.ts'),
      '/** @ensures{p} forall (x: int ∈ [0, 1000000000000000000000000000000]) { f(x) >= 0 } */\nexport function f(x: number): number { return x; }\n',
    );
    process.chdir(dir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(dir, { recursive: true, force: true });
  });

  test('mirrors the source path under the out root', () => {
    const [a] = writeArtifacts([path.join('sub', 'a.ts')], OUT);
    expect(a!.outFile).toBe(path.join(OUT, 'sub', 'a.ts.lean'));
    const lean = fs.readFileSync(a!.outFile!, 'utf8');
    expect(lean).toContain('import ThalesDsl');
    expect(lean).toContain('#thales_prove');
    expect(a!.annotations).toHaveLength(1);
    expect(a!.invalid).toHaveLength(0);
  });

  test('annotation-free files get an entry but no artifact', () => {
    const [p] = writeArtifacts(['plain.ts'], OUT);
    expect(p).toEqual({
      sourceFile: 'plain.ts',
      annotations: [],
      invalid: [],
      untried: [],
    });
    expect(fs.existsSync(path.join(OUT, 'plain.ts.lean'))).toBe(false);
  });

  test('extension-only siblings get distinct artifacts', () => {
    const arts = writeArtifacts(['x.ts', 'x.tsx'], OUT);
    expect(arts.map((a) => a.outFile)).toEqual([
      path.join(OUT, 'x.ts.lean'),
      path.join(OUT, 'x.tsx.lean'),
    ]);
    for (const a of arts) expect(fs.existsSync(a.outFile!)).toBe(true);
  });

  test('untried annotations travel on the artifact entry', () => {
    const [h] = writeArtifacts(['huge.ts'], OUT);
    expect(h!.untried).toHaveLength(1);
    expect(h!.untried[0]!.kind).toBe('unsupported-range');
    expect(h!.untried[0]!.annotation.propertyName).toBe('p');
    // The artifact is still written: it documents the skip as a comment.
    expect(fs.readFileSync(h!.outFile!, 'utf8')).toContain('-- not tried');
  });

  test('refuses files outside the current directory', () => {
    expect(() => writeArtifacts([path.join('..', 'nope.ts')], OUT)).toThrow(
      LemmaError,
    );
  });
});
