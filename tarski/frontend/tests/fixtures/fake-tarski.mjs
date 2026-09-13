#!/usr/bin/env node
// A stand-in for `.lake/build/bin/tarski`, so the runner's real spawn
// path is exercised without a Lean toolchain.
//
// It reads the ESTree document it was handed and obeys the first string
// literal in it that begins `fake: `. Every run test in the fake tree
// carries one, in a declaration that is inert for the real evaluator, so
// the same files drive the unit tests and `test262-e2e.test.ts` — and
// that e2e is what ties these exit codes and stderr shapes to the ones
// the binary actually produces.
//
//   fake: exit 0
//   fake: exit 1 <the stderr line>
//   fake: exit 3 unsupported: <kind>
//   fake: exit 2 <the stderr line>
//   fake: timeout
//
// No marker means exit 0, which is what the harness preludes alone do.

import { readFileSync } from "node:fs";

/** The first `fake: …` string literal anywhere in the document. */
function marker(node) {
  if (node === null || typeof node !== "object") return undefined;
  if (Array.isArray(node)) {
    for (const child of node) {
      const found = marker(child);
      if (found !== undefined) return found;
    }
    return undefined;
  }
  if (
    node.type === "Literal" &&
    typeof node.value === "string" &&
    node.value.startsWith("fake: ")
  ) {
    return node.value.slice("fake: ".length);
  }
  for (const child of Object.values(node)) {
    const found = marker(child);
    if (found !== undefined) return found;
  }
  return undefined;
}

const [command, file] = process.argv.slice(2);
if (command !== "run" || file === undefined) {
  process.stderr.write("usage: fake-tarski run <file.json>\n");
  process.exit(2);
}

const instruction = marker(JSON.parse(readFileSync(file, "utf8"))) ?? "exit 0";

if (instruction === "timeout") {
  // Busy-wait past any timeout the runner imposes. `spawnSync` kills the
  // process, which is the arm being exercised.
  for (;;) {}
}

const exit = /^exit (\d+)\s*(.*)$/s.exec(instruction);
if (exit === null) {
  process.stderr.write(`fake-tarski: unknown instruction ${instruction}\n`);
  process.exit(2);
}
if (exit[2].length > 0) process.stderr.write(`${exit[2]}\n`);
process.exit(Number(exit[1]));
