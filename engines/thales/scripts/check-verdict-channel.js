#!/usr/bin/env node
// Checks the JSON verdict-line contract between ThalesDsl's #thales_prove
// command elaborator and the CLI: one parseable line per command on stdout,
// failures contained per command, clean exit.

const { spawnSync } = require('node:child_process');
const path = require('node:path');

const engineRoot = path.resolve(__dirname, '..');
const fixture = path.join('tests', 'fixtures', 'verdict-channel.lean');

const SZS = new Set([
  'Theorem',
  'CounterSatisfiable',
  'GaveUp',
  'Timeout',
  'Inappropriate',
  'NotTried',
  'Error',
]);

const failures = [];
function check(cond, message) {
  if (!cond) failures.push(message);
}

const run = spawnSync('lake', ['env', 'lean', fixture], {
  cwd: engineRoot,
  encoding: 'utf8',
  timeout: 300_000,
});

check(run.error === undefined, `failed to run lake: ${run.error}`);
check(
  run.status === 0,
  `expected exit 0, got ${run.status}\nstderr:\n${run.stderr}`,
);

const lines = (run.stdout ?? '').split('\n').filter((l) => l.trim() !== '');
check(
  lines.length === 4,
  `expected 4 verdict lines (one per command), got ${lines.length}:\n${run.stdout}`,
);

const verdicts = [];
for (const line of lines) {
  let v;
  try {
    v = JSON.parse(line);
  } catch {
    check(false, `stdout line is not valid JSON: ${line}`);
    continue;
  }
  check(
    Array.isArray(v.identity) &&
      v.identity.length === 3 &&
      v.identity.every((s) => typeof s === 'string'),
    `identity must be [file, function, property]: ${line}`,
  );
  check(SZS.has(v.szs), `unknown szs status ${JSON.stringify(v.szs)}: ${line}`);
  check(
    typeof v.reason === 'string' && v.reason.length > 0,
    `reason must be a non-empty string: ${line}`,
  );
  verdicts.push(v);
}

if (verdicts.length === 4) {
  const functions = verdicts.map((v) => v.identity[1]);
  check(
    JSON.stringify(functions) === JSON.stringify(['add', 'sub', 'bad', 'tail']),
    `verdicts out of order: ${functions.join(', ')}`,
  );
  check(
    verdicts[2].szs === 'Error',
    `the failing command must report Error, got ${verdicts[2].szs}`,
  );
  for (const i of [0, 1, 3]) {
    check(
      verdicts[i].szs === 'NotTried',
      `stub command ${i} must report NotTried, got ${verdicts[i].szs}`,
    );
  }
}

if (failures.length > 0) {
  console.error('verdict-channel check FAILED:');
  for (const f of failures) console.error(`  - ${f}`);
  process.exit(1);
}
console.log(`verdict-channel check passed (${verdicts.length} verdicts)`);
