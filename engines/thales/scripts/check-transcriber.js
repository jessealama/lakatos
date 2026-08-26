#!/usr/bin/env node
// End-to-end check of the tsc-AST-to-DSL transcriber: transcribe the tracer
// fixture with the compiled front end, run the emitted .lean file, and
// assert the expected per-annotation verdict lines. Requires the root
// package to be built (npx tsc -p tsconfig.json from the repo root).

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { checker, engineRoot, frontend, repoRoot } from "./harness.js";

const { transcribeFile } = await frontend("transcribe");
const { parseVerdicts, runArtifact } = await frontend("run");

// [function, szs, reasonPattern?] per annotation, in annotation order.
const EXPECTED = [
  ["add", "Theorem"],
  ["fetchTotal", "Inappropriate", /AwaitExpression.*8:10/],
  ["Counter#bump", "Inappropriate", /ClassDeclaration.*13:3/],
];

const { check, done } = checker("transcriber");

process.chdir(repoRoot); // the fixture path is the annotations' identity file
const lean = transcribeFile(
  path.join("engines", "thales", "tests", "fixtures", "tracer.ts"),
);

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "thales-transcriber-"));
const leanFile = path.join(tmp, "tracer.lean");
fs.writeFileSync(leanFile, lean);

const run = runArtifact(engineRoot, leanFile);

check(run.error === undefined, `failed to run lake: ${run.error}`);
check(
  run.status === 0,
  `expected exit 0, got ${run.status}\nstderr:\n${run.stderr}`,
);

const { verdicts, diagnostics, messages } = parseVerdicts(run.stdout ?? "");
check(
  diagnostics.length === 0,
  `unframed stdout line(s):\n${diagnostics.join("\n")}`,
);
for (const m of messages) check(false, m);
check(
  verdicts.length === EXPECTED.length,
  `expected ${EXPECTED.length} verdict lines, got ${verdicts.length}:\n${run.stdout}`,
);

if (verdicts.length === EXPECTED.length) {
  for (const [i, [fn, szs, reasonPattern]] of EXPECTED.entries()) {
    const v = verdicts[i];
    check(
      JSON.stringify(v.identity.slice(0, 2)) ===
        JSON.stringify(["engines/thales/tests/fixtures/tracer.ts", fn]),
      `verdict ${i}: expected identity for '${fn}', got ${JSON.stringify(v.identity)}`,
    );
    check(
      v.szs === szs,
      `verdict ${i}: expected ${szs}, got ${JSON.stringify(v.szs)}`,
    );
    if (reasonPattern !== undefined) {
      check(
        reasonPattern.test(v.reason),
        `verdict ${i}: reason ${JSON.stringify(v.reason)} does not match ${reasonPattern}`,
      );
    }
  }
}

fs.rmSync(tmp, { recursive: true, force: true });

done("tracer fixture");
