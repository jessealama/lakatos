import { afterAll, beforeAll, describe, expect, test } from 'vitest';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { LemmaError } from '../../../../lemma/src/errors.js';
import { writeArtifacts } from '../src/artifacts.js';

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
    process.chdir(dir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(dir, { recursive: true, force: true });
  });

  test('mirrors the source path under the out root', () => {
    const [a] = writeArtifacts([path.join('sub', 'a.ts')]);
    expect(a!.outFile).toBe(path.join('.thales', 'sub', 'a.lean'));
    const lean = fs.readFileSync(a!.outFile!, 'utf8');
    expect(lean).toContain('import ThalesDsl');
    expect(lean).toContain('#thales_prove');
    expect(a!.annotations).toHaveLength(1);
    expect(a!.invalid).toHaveLength(0);
  });

  test('annotation-free files get an entry but no artifact', () => {
    const [p] = writeArtifacts(['plain.ts']);
    expect(p).toEqual({ sourceFile: 'plain.ts', annotations: [], invalid: [] });
    expect(fs.existsSync(path.join('.thales', 'plain.lean'))).toBe(false);
  });

  test('refuses files outside the current directory', () => {
    expect(() => writeArtifacts([path.join('..', 'nope.ts')])).toThrow(
      LemmaError,
    );
  });
});
