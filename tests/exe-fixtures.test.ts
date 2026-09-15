import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { spawnSync } from "node:child_process";
import {
  copyFileSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  rmSync,
} from "node:fs";
import * as path from "node:path";
import { executeSource, type ExeDeps } from "../src/exe.js";
import { ensureBinary } from "../tarski/frontend/src/binary.js";
import { findTarskiRoot } from "../tarski/frontend/src/test262/paths.js";

// Every `@ensures` fixture in the repo, run under `lakatos exe` and under
// Node, with the two compared. This is what says the evaluator is an
// evaluator rather than a plausible-looking one: the same programs
// `lakatos prove` proves theorems about, executed, with an engine as the
// control.
//
// It needs the real binary, so it runs where `test262-e2e.test.ts` runs —
// `tarski.yml`, the one job with Node and Lean — and skips elsewhere.
const e2e = process.env.LAKATOS_TARSKI_E2E === "1";

const REPO = process.cwd();

/** The four fixture roots. "Every `@ensures` fixture in the repo" is the
 * issue's phrase, and it is not only thales's. */
const ROOTS = [
  "engines/thales/tests/fixtures",
  "engines/thales/tests/conformance",
  "engines/pabst/tests/fixtures",
  "spec/fixtures",
];

function walk(dir: string, out: string[]): string[] {
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) walk(full, out);
    else if (
      entry.name.endsWith(".ts") &&
      !entry.name.endsWith(".d.ts") &&
      !entry.name.endsWith(".test.ts")
    )
      out.push(full);
  }
  return out;
}

/** The corpus, as repo-relative posix paths, sorted. */
function corpus(): string[] {
  const files: string[] = [];
  for (const root of ROOTS) walk(path.join(REPO, root), files);
  return files
    .filter((f) => readFileSync(f, "utf8").includes("@ensures"))
    .map((f) => path.relative(REPO, f).split(path.sep).join("/"))
    .sort();
}

/**
 * The fixtures the evaluator refuses, each with the node kind it named.
 * Measured, not predicted: a row that moves is either a slice that landed
 * or a regression, and either way it belongs in a diff.
 *
 * Sixteen of the corpus's two hundred and seventy-six. The six
 * `ImportDeclaration` rows are the multi-file fixtures, which `exe`
 * refuses by design — it resolves no module graph. The rest is syntax
 * outside the evaluated fragment: BigInt, a regular expression, `&`,
 * `??`, a computed *class* key, a private accessor, an `async` function,
 * and an `export default class` with no name, which is a class
 * declaration with no `id` once the module syntax is off it. The four
 * fixtures refused for a template literal left this map when #395
 * landed, and the one `Parameter` row — a rest constructor parameter —
 * left it when #394 did.
 */
const UNSUPPORTED: Record<string, string> = {
  "engines/pabst/tests/fixtures/e2e/bounded.ts": "BigIntLiteral",
  "engines/pabst/tests/fixtures/e2e/readme-example.ts": "BigIntLiteral",
  "engines/pabst/tests/fixtures/e2e/regex-guard.ts": "RegularExpressionLiteral",
  "engines/thales/tests/conformance/inappropriate/await-remote.ts":
    "FunctionDeclaration async",
  "engines/thales/tests/conformance/inappropriate/bare-import/main.ts":
    "ImportDeclaration",
  "engines/thales/tests/conformance/inappropriate/import-cycle/main.ts":
    "ImportDeclaration",
  "engines/thales/tests/conformance/inappropriate/unmodeled-operator.ts":
    "BinaryExpression &",
  "engines/thales/tests/conformance/theorem/imported-constants/main.ts":
    "ImportDeclaration",
  "engines/thales/tests/conformance/theorem/imported-scale/main.ts":
    "ImportDeclaration",
  "engines/thales/tests/fixtures/tracer.ts": "FunctionDeclaration async",
  "spec/fixtures/attach/reject/anonymous-class.ts": "ClassDeclaration",
  "spec/fixtures/attach/reject/computed-name.ts": "ComputedPropertyName",
  "spec/fixtures/attach/reject/private-getter.ts": "MethodDefinition private",
  "spec/fixtures/binder/reject/ctor-param-optional.ts": "LogicalExpression ??",
  "spec/fixtures/island/accept/reexported-import.ts": "ImportDeclaration",
  "spec/fixtures/island/reject/imported-not-reexported.ts": "ImportDeclaration",
};

/**
 * A fixture the evaluator supports but whose run differs from Node's, for
 * a reason outside this slice. Empty, and meant to stay that way: a row
 * here needs the issue it waits on written beside it.
 */
const DISAGREES: Record<string, string> = {};

/** One `tarski exec`, under a timeout: a fixture that diverges must not
 * take the suite with it. `exe` itself imposes none — a program hangs as
 * it would under `node` — but a batch of 276 is a different contract. */
const EXEC_TIMEOUT_MS = 30_000;

/** The whole corpus, run once: two spawns a fixture is enough. */
const MEASURE_TIMEOUT_MS = 600_000;

describe.runIf(e2e)(
  "every @ensures fixture, on the evaluator and on Node",
  () => {
    const files = corpus();
    const scratch = path.join(REPO, ".lakatos", "exe-fixtures");
    /** The node kind each refused fixture named. */
    const refused: Record<string, string> = {};
    /** What each supported fixture did differently from Node. */
    const disagreed: Record<string, string> = {};

    // One pass, in a hook, so the two claims below are two readings of one
    // measurement rather than two runs of the same 280 programs.
    beforeAll(() => {
      rmSync(scratch, { recursive: true, force: true });
      mkdirSync(scratch, { recursive: true });
      const binary = ensureBinary(findTarskiRoot());
      expect(binary.kind, JSON.stringify(binary)).toBe("ready");
      const deps: ExeDeps = {
        ensureBinary: () => binary,
        runDocument: (bin, documentPath) =>
          spawnSync(bin, ["exec", documentPath], {
            encoding: "utf8",
            timeout: EXEC_TIMEOUT_MS,
            maxBuffer: 256 * 1024 * 1024,
          }),
      };

      for (const file of files) {
        const outDir = path.join(scratch, file);
        const outcome = executeSource(
          readFileSync(path.join(REPO, file), "utf8"),
          file,
          outDir,
          deps,
        );
        if (outcome.kind === "unsupported") {
          refused[file] = outcome.node;
          continue;
        }
        if (outcome.kind !== "ran") {
          disagreed[file] = `exe: ${JSON.stringify(outcome)}`;
          continue;
        }
        // Node runs the very same stripped text, under the extension that
        // makes it a module — the fixtures are module code.
        const base = path.basename(file).replace(/\.ts$/, "");
        const mjs = path.join(outDir, `${base}.mjs`);
        copyFileSync(path.join(outDir, `${base}.js`), mjs);
        const node = spawnSync(process.execPath, [mjs], {
          encoding: "utf8",
          timeout: EXEC_TIMEOUT_MS,
        });
        if (outcome.stdout !== node.stdout || outcome.status !== node.status) {
          disagreed[file] =
            `exe ${outcome.status} ${JSON.stringify(outcome.stdout)} / ` +
            `node ${node.status} ${JSON.stringify(node.stdout)}`;
        }
      }
    }, MEASURE_TIMEOUT_MS);

    afterAll(() => {
      rmSync(scratch, { recursive: true, force: true });
    });

    // An emptied fixture root would otherwise make this whole suite pass
    // by having nothing to compare.
    it("has a corpus to compare", () => {
      expect(files.length).toBeGreaterThan(250);
    });

    it("refuses exactly the fixtures it is pinned to refuse", () => {
      expect(refused).toEqual(UNSUPPORTED);
    });

    // Node is the control: what it prints and how it exits is what the
    // evaluator has to match. Compared by key, since a row in DISAGREES
    // carries the issue it waits on and the measurement carries the
    // difference it saw.
    it("agrees with Node on every fixture it supports", () => {
      expect(Object.keys(disagreed).sort()).toEqual(
        Object.keys(DISAGREES).sort(),
      );
    });
  },
);
