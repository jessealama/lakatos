#!/usr/bin/env node
// Checks the JSON verdict-line contract between ThalesDsl's #thales_prove
// command elaborator and the CLI: one parseable line per command on stdout,
// in command order, failures contained per command, clean exit.

import { spawnSync } from 'node:child_process';
import * as path from 'node:path';
import { fileURLToPath } from 'node:url';

const engineRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);

// Verdict lines are sentinel-framed: stdout is also Lean's diagnostic
// stream, and only framed lines are part of the contract.
const SENTINEL = 'thales-verdict:';

const SZS = new Set([
  'Theorem',
  'CounterSatisfiable',
  'GaveUp',
  'Timeout',
  'Inappropriate',
  'NotTried',
  'Error',
]);

// Expected [function, szs, reasonPattern?] sequence per fixture, in
// command order; reasonPattern, when present, must match the reason.
const FIXTURES = [
  {
    file: 'verdict-channel.lean',
    expected: [
      ['add', 'NotTried'],
      ['sub', 'NotTried'],
      ['bad', 'Error'],
      ['opq', 'Error', /YieldExpression.*3:14/],
      ['tail', 'NotTried'],
    ],
  },
  {
    file: 'theorem-arith.lean',
    expected: Array.from({ length: 8 }, () => ['add', 'Theorem']),
  },
  {
    file: 'theorem-inappropriate.lean',
    expected: [
      ['add', 'Theorem'],
      ['fetchTotal', 'Inappropriate', /AwaitExpression/],
      ['spin', 'Inappropriate', /WhileStatement/],
      ['sq', 'Theorem'],
    ],
  },
];

const failures = [];
function check(cond, message) {
  if (!cond) failures.push(message);
}

for (const { file, expected } of FIXTURES) {
  const fixture = path.join('tests', 'fixtures', file);
  const run = spawnSync('lake', ['env', 'lean', fixture], {
    cwd: engineRoot,
    encoding: 'utf8',
    timeout: 300_000,
  });

  check(run.error === undefined, `${file}: failed to run lake: ${run.error}`);
  check(
    run.status === 0,
    `${file}: expected exit 0, got ${run.status}\nstderr:\n${run.stderr}`,
  );

  const allLines = (run.stdout ?? '')
    .split('\n')
    .filter((l) => l.trim() !== '');
  const lines = allLines.filter((l) => l.startsWith(SENTINEL));
  check(
    allLines.length === lines.length,
    `${file}: unframed stdout line(s):\n${allLines
      .filter((l) => !l.startsWith(SENTINEL))
      .join('\n')}`,
  );
  check(
    lines.length === expected.length,
    `${file}: expected ${expected.length} verdict lines, got ${lines.length}:\n${run.stdout}`,
  );

  const verdicts = [];
  for (const line of lines) {
    let v;
    try {
      v = JSON.parse(line.slice(SENTINEL.length));
    } catch {
      check(false, `${file}: stdout line is not valid JSON: ${line}`);
      continue;
    }
    check(
      Array.isArray(v.identity) &&
        v.identity.length === 3 &&
        v.identity.every((s) => typeof s === 'string'),
      `${file}: identity must be [file, function, property]: ${line}`,
    );
    check(
      SZS.has(v.szs),
      `${file}: unknown szs status ${JSON.stringify(v.szs)}: ${line}`,
    );
    check(
      typeof v.reason === 'string' && v.reason.length > 0,
      `${file}: reason must be a non-empty string: ${line}`,
    );
    verdicts.push(v);
  }

  if (verdicts.length === expected.length) {
    const got = verdicts.map((v) => [v.identity[1], v.szs]);
    const want = expected.map(([fn, szs]) => [fn, szs]);
    check(
      JSON.stringify(got) === JSON.stringify(want),
      `${file}: expected verdicts ${JSON.stringify(want)}, got ${JSON.stringify(got)}`,
    );
    for (const [i, [, , reasonPattern]] of expected.entries()) {
      if (reasonPattern !== undefined) {
        check(
          reasonPattern.test(verdicts[i].reason),
          `${file}: verdict ${i} reason ${JSON.stringify(verdicts[i].reason)} does not match ${reasonPattern}`,
        );
      }
    }
  }
}

if (failures.length > 0) {
  console.error('verdict-channel check FAILED:');
  for (const f of failures) console.error(`  - ${f}`);
  process.exit(1);
}
console.log(`verdict-channel check passed (${FIXTURES.length} fixtures)`);
