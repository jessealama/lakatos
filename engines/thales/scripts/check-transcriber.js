#!/usr/bin/env node
// End-to-end check of the tsc-AST-to-DSL transcriber: transcribe the tracer
// fixture with the compiled front end, run the emitted .lean file, and
// assert the expected per-annotation verdict lines. Requires the root
// package to be built (npx tsc -p tsconfig.json from the repo root).

import { spawnSync } from 'node:child_process';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { fileURLToPath } from 'node:url';

const engineRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);
const repoRoot = path.resolve(engineRoot, '..', '..');

// Verdict lines are sentinel-framed; unframed stdout is diagnostics and
// must not appear when running a clean fixture.
const SENTINEL = 'thales-verdict:';

// [function, szs, reasonPattern?] per annotation, in annotation order.
const EXPECTED = [
  ['add', 'Theorem'],
  ['fetchTotal', 'Inappropriate', /AwaitExpression.*8:10/],
  ['Counter#bump', 'Inappropriate', /ClassDeclaration.*13:3/],
];

const failures = [];
function check(cond, message) {
  if (!cond) failures.push(message);
}

const { transcribeFile } = await import(
  path.join(
    repoRoot,
    'dist',
    'engines',
    'thales',
    'frontend',
    'src',
    'transcribe.js',
  )
);

process.chdir(repoRoot); // the fixture path is the annotations' identity file
const lean = transcribeFile(
  path.join('engines', 'thales', 'tests', 'fixtures', 'tracer.ts'),
);

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'thales-transcriber-'));
const leanFile = path.join(tmp, 'tracer.lean');
fs.writeFileSync(leanFile, lean);

const run = spawnSync('lake', ['env', 'lean', leanFile], {
  cwd: engineRoot,
  encoding: 'utf8',
  timeout: 300_000,
});

check(run.error === undefined, `failed to run lake: ${run.error}`);
check(
  run.status === 0,
  `expected exit 0, got ${run.status}\nstderr:\n${run.stderr}`,
);

const allLines = (run.stdout ?? '').split('\n').filter((l) => l.trim() !== '');
const lines = allLines.filter((l) => l.startsWith(SENTINEL));
check(
  allLines.length === lines.length,
  `unframed stdout line(s):\n${allLines
    .filter((l) => !l.startsWith(SENTINEL))
    .join('\n')}`,
);
check(
  lines.length === EXPECTED.length,
  `expected ${EXPECTED.length} verdict lines, got ${lines.length}:\n${run.stdout}`,
);

if (lines.length === EXPECTED.length) {
  for (const [i, [fn, szs, reasonPattern]] of EXPECTED.entries()) {
    let v;
    try {
      v = JSON.parse(lines[i].slice(SENTINEL.length));
    } catch {
      check(false, `stdout line is not valid JSON: ${lines[i]}`);
      continue;
    }
    check(
      JSON.stringify(v.identity?.slice(0, 2)) ===
        JSON.stringify(['engines/thales/tests/fixtures/tracer.ts', fn]),
      `verdict ${i}: expected identity for '${fn}', got ${lines[i]}`,
    );
    check(v.szs === szs, `verdict ${i}: expected ${szs}, got ${lines[i]}`);
    if (reasonPattern !== undefined) {
      check(
        reasonPattern.test(v.reason),
        `verdict ${i}: reason ${JSON.stringify(v.reason)} does not match ${reasonPattern}`,
      );
    }
  }
}

fs.rmSync(tmp, { recursive: true, force: true });

if (failures.length > 0) {
  console.error('transcriber check FAILED:');
  for (const f of failures) console.error(`  - ${f}`);
  process.exit(1);
}
console.log('transcriber check passed (tracer fixture)');
