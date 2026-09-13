// What to do with one test file: run this text, file it as not run, or
// skip it entirely.
//
// INTERPRETING.md fixes the assembly. The two preludes `sta.js` and
// `assert.js` come first, then the file's `includes` in the order given,
// then the test. The whole assembly is one script, so the `"use strict";`
// directive goes at the top of the whole thing rather than on the test
// alone. A `raw` test is the exception: it is run exactly as written,
// with no harness at all.
//
// The epic is strict mode only, so a `noStrict` test is not run rather
// than failed, and so is a `raw` test whose own text does not start
// strict. `async` needs the job queue, and `module` needs modules;
// neither is in the epic. A parse- or resolution-phase negative test is
// not scored at all (the parser is TypeScript's, not this evaluator's),
// and neither is `intl402`.

import { readdirSync, statSync } from "node:fs";
import path from "node:path";
import { parseFrontMatter } from "./frontmatter.js";

/** Why a test was counted but not run. Each is a column of its own. */
export type NotRunReason = "noStrict" | "raw" | "async" | "module";

/** Why a test is outside the table entirely. */
export type SkipReason = "intl402" | "parse-negative" | "resolution-negative";

/** What the runner does with one test. */
export type Plan =
  | { kind: "run"; source: string; negative?: { type: string } }
  | { kind: "not-run"; reason: NotRunReason }
  | { kind: "skip"; reason: SkipReason };

/**
 * The runner's own machinery failing, as distinct from a test failing: an
 * `includes` naming a harness file that is not there. The runner files it
 * as `harness-error`, never as `fail`.
 */
export class HarnessError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "HarnessError";
  }
}

/** The two preludes every non-`raw` test gets, in this order. */
const PRELUDES = ["sta.js", "assert.js"];

/** Whether the text's first token is a `"use strict"` directive. */
function startsStrict(source: string): boolean {
  // Leading whitespace, line comments, and block comments, then the
  // directive in either quote. The suite's five strict `raw` tests are
  // all of this shape (a copyright comment, then the directive).
  /* v8 ignore next 3 -- the pattern matches the empty string, so `exec`
     always answers; the fallback is the type asking. */
  const head =
    /^(?:\s|\/\/[^\n]*\n|\/\*(?:[^*]|\*(?!\/))*\*\/)*/.exec(source)?.[0]
      .length ?? 0;
  return /^(?:"use strict"|'use strict')\s*;/.test(source.slice(head));
}

/**
 * What to do with the test at `relPath` (relative to the test262 root),
 * whose text is `source`. `readHarness` reads one file out of the
 * checkout's `harness/` directory, and throws `HarnessError` when there
 * is none.
 */
export function planTest(
  relPath: string,
  source: string,
  readHarness: (name: string) => string,
): Plan {
  // Order matters: a test can be several of these at once, and the first
  // answer is the one that explains it best.
  if (relPath.split(path.sep).join("/").startsWith("test/intl402/")) {
    return { kind: "skip", reason: "intl402" };
  }
  const front = parseFrontMatter(source);
  if (front.negative?.phase === "parse")
    return { kind: "skip", reason: "parse-negative" };
  if (front.negative?.phase === "resolution") {
    return { kind: "skip", reason: "resolution-negative" };
  }
  if (front.flags.includes("module"))
    return { kind: "not-run", reason: "module" };
  if (front.flags.includes("raw")) {
    // No harness and no modification, says INTERPRETING.md. A raw test
    // that is not already strict cannot be run at all here.
    if (!startsStrict(source)) return { kind: "not-run", reason: "raw" };
    return { kind: "run", source, ...negativeOf(front.negative) };
  }
  if (front.flags.includes("noStrict"))
    return { kind: "not-run", reason: "noStrict" };
  if (front.flags.includes("async"))
    return { kind: "not-run", reason: "async" };

  // `onlyStrict` and the unflagged default are the same run here, the
  // epic being strict-mode only.
  const parts = ['"use strict";'];
  for (const name of [...PRELUDES, ...front.includes])
    parts.push(readHarness(name));
  parts.push(source);
  return {
    kind: "run",
    source: parts.join("\n"),
    ...negativeOf(front.negative),
  };
}

/** The runtime-phase negative expectation, if there is one. */
function negativeOf(negative: { phase: string; type: string } | undefined): {
  negative?: { type: string };
} {
  // Only the runtime phase reaches here: parse and resolution are skips.
  return negative === undefined ? {} : { negative: { type: negative.type } };
}

/**
 * Every test under each slice, sorted, as paths relative to the test262
 * root. A slice is a directory or a single file. `_FIXTURE.js` files are
 * a module test's imports, not tests.
 */
export function listTests(
  test262Root: string,
  slices: readonly string[],
): string[] {
  const out: string[] = [];
  for (const slice of slices) {
    const absolute = path.join(test262Root, slice);
    if (statSync(absolute).isDirectory()) {
      for (const entry of readdirSync(absolute, {
        recursive: true,
        withFileTypes: true,
      })) {
        if (!entry.isFile()) continue;
        const relative = path.relative(
          test262Root,
          path.join(entry.parentPath, entry.name),
        );
        if (isTest(entry.name)) out.push(relative);
      }
    } else if (isTest(path.basename(absolute))) {
      out.push(path.relative(test262Root, absolute));
    }
  }
  return out.sort();
}

/** A `.js` file that is a test rather than a module fixture. */
function isTest(name: string): boolean {
  return name.endsWith(".js") && !name.endsWith("_FIXTURE.js");
}
