#!/usr/bin/env node
// Checks the JSON verdict-line contract between ThalesDsl's #thales_prove
// command elaborator and the CLI: one parseable line per command on stdout,
// in command order, failures contained per command, clean exit. The channel
// itself — the sentinel, the parse, the verdict validation, the lake
// invocation and its timeout — comes from the built frontend, so this
// checks production's reader rather than a second copy of it.

import * as path from 'node:path';
import { checker, engineRoot, frontend } from './harness.js';

const { parseVerdicts, runArtifact } = await frontend('run');

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
    expected: [
      ...Array.from({ length: 7 }, () => [
        'add',
        'Theorem',
        /proved by a decision procedure over the bounded domain, kernel-checked as/,
      ]),
      // Integer binder values coerced into a binary64 body: narrow enough
      // for the kernel to enumerate, then wide enough that only evaluation
      // can. The trust wording is read off each proof's axioms.
      [
        'dbl',
        'Theorem',
        /proved by a decision procedure over the bounded domain, kernel-checked as/,
      ],
      ['dbl', 'Theorem', /trusted from evaluation rather than checked by the kernel/],
      [
        'add',
        'Theorem',
        /proved by a decision procedure over the bounded domain, kernel-checked as/,
      ],
    ],
  },
  {
    file: 'countersatisfiable.lean',
    expected: [
      ['bump', 'CounterSatisfiable', /false/, { x: 0 }],
      ['sq', 'CounterSatisfiable', /false/, { x: 0 }],
      ['comm', 'CounterSatisfiable', /false/, { a: 0, b: 1 }],
      ['bump', 'GaveUp', /^the property is false on its bounded domain$/],
      // Falsity outlives the witness search that ran out of budget: the
      // counterexample is gone, the verdict is not, and it is not a Timeout.
      ['bump', 'GaveUp', /^the property is false on its bounded domain$/],
    ],
  },
  // The symbolic rungs have no binary64 theory to work with yet, so an
  // unbounded binder leaves a residual goal rather than a proof. The
  // residual is the point: it names the fact the theory worklist needs.
  {
    file: 'gaveup-generic.lean',
    expected: [
      ['dbl', 'GaveUp', /unsolved goal:[\s\S]*Float\.ofInt/],
      ['dbl', 'GaveUp', /unsolved goal:[\s\S]*Float\.ofInt/],
      ['dbl', 'GaveUp', /unsolved goal:[\s\S]*Float\.ofInt/],
    ],
  },
  {
    file: 'gaveup-grind.lean',
    expected: [['mul', 'GaveUp', /unsolved goal:[\s\S]*Float\.ofInt/]],
  },
  {
    file: 'gaveup-goal.lean',
    expected: [
      ['bump', 'GaveUp', /unsolved goal:[\s\S]*\+ 1 = /],
      // Bounded, but past the evaluation cap: no tier can settle it inside
      // the annotation's budget, so the attempt reports as budget-bound.
      ['wide', 'Timeout', /heartbeat budget/],
    ],
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
      ['slow', 'Timeout', /thales\.heartbeats = 1\)$/],
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

const { check, done } = checker('verdict-channel');

for (const { file, expected } of FIXTURES) {
  const run = runArtifact(
    engineRoot,
    path.join(engineRoot, 'tests', 'fixtures', file),
  );

  check(run.error === undefined, `${file}: failed to run lake: ${run.error}`);
  check(
    run.status === 0,
    `${file}: expected exit 0, got ${run.status}\nstderr:\n${run.stderr}`,
  );

  const { verdicts, diagnostics, messages } = parseVerdicts(run.stdout ?? '');
  check(
    diagnostics.length === 0,
    `${file}: unframed stdout line(s):\n${diagnostics.join('\n')}`,
  );
  for (const m of messages) check(false, `${file}: ${m}`);
  check(
    verdicts.length === expected.length,
    `${file}: expected ${expected.length} verdict lines, got ${verdicts.length}:\n${run.stdout}`,
  );

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

done(`${FIXTURES.length} fixtures`);
