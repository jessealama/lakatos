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

// Must match PROVE_STATUSES in src/envelope.ts; the root suite pins the
// two together.
const SZS = new Set([
  'Theorem',
  'CounterSatisfiable',
  'Inappropriate',
  'GaveUp',
  'Timeout',
  'NotTried',
  'Error',
]);

// Expected [function, szs, reasonPattern?, counterexample?] sequence per
// fixture, in command order; reasonPattern, when present, must match the
// reason; counterexample, when present, must deep-equal the verdict's
// (and only expected entries may carry one).
const FIXTURES = [
  {
    file: 'verdict-channel.lean',
    expected: [
      ['add', 'NotTried'],
      ['sub', 'NotTried'],
      ['bad', 'Error'],
      ['opq', 'Inappropriate', /YieldExpression.*3:14/],
      ['tail', 'NotTried'],
      ['viaAw', 'Inappropriate', /AwaitExpression/],
    ],
  },
  {
    file: 'theorem-arith.lean',
    expected: Array.from({ length: 8 }, () => [
      'add',
      'Theorem',
      /proved by a decision procedure over the bounded domain, kernel-checked as/,
    ]),
  },
  {
    file: 'countersatisfiable.lean',
    expected: [
      ['bump', 'CounterSatisfiable', /false/, { x: 0 }],
      ['sq', 'CounterSatisfiable', /false/, { x: 0 }],
      ['comm', 'CounterSatisfiable', /false/, { a: 0, b: 1 }],
      ['bump', 'GaveUp', /false/],
    ],
  },
  {
    file: 'theorem-generic.lean',
    expected: [
      ['dbl', 'Theorem', /proved by generic proof search, kernel-checked as/],
      ['dbl', 'Theorem', /proved by generic proof search, kernel-checked as/],
      ['dbl', 'Theorem', /proved by generic proof search, kernel-checked as/],
    ],
  },
  {
    file: 'theorem-grind.lean',
    expected: [
      ['mul', 'Theorem', /proved by generic proof search, kernel-checked as/],
    ],
  },
  {
    file: 'gaveup-goal.lean',
    expected: [['bump', 'GaveUp', /unsolved goal:[\s\S]*x \+ 1 = x/]],
  },
  {
    file: 'recdepth.lean',
    expected: [
      ['bump', 'GaveUp', /^unsolved goal:[\s\S]*bump/],
      ['bump', 'Error', /^property elaboration failed/],
      ['bump', 'Theorem'],
    ],
  },
  {
    file: 'timeout.lean',
    expected: [
      ['slow', 'Timeout', /heartbeat budget/],
      ['add', 'Theorem'],
      ['slow', 'Timeout', /heartbeat budget/],
    ],
  },
  {
    file: 'theorem-rescue.lean',
    expected: [['dbl', 'Theorem']],
  },
  {
    file: 'theorem-inappropriate.lean',
    expected: [
      ['add', 'Theorem'],
      ['fetchTotal', 'Inappropriate', /AwaitExpression/],
      ['spin', 'Inappropriate', /WhileStatement/],
      ['sq', 'Theorem'],
      ['dup', 'Theorem'],
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
    for (const [i, [, , reasonPattern, counterexample]] of expected.entries()) {
      if (reasonPattern !== undefined) {
        check(
          reasonPattern.test(verdicts[i].reason),
          `${file}: verdict ${i} reason ${JSON.stringify(verdicts[i].reason)} does not match ${reasonPattern}`,
        );
      }
      check(
        JSON.stringify(verdicts[i].counterexample) ===
          JSON.stringify(counterexample),
        `${file}: verdict ${i} counterexample ${JSON.stringify(verdicts[i].counterexample)}, expected ${JSON.stringify(counterexample)}`,
      );
    }
  }
}

if (failures.length > 0) {
  console.error('verdict-channel check FAILED:');
  for (const f of failures) console.error(`  - ${f}`);
  process.exit(1);
}
console.log(`verdict-channel check passed (${FIXTURES.length} fixtures)`);
