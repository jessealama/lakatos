// `lakatos exe`'s pipeline, without the CLI's input or output: strip a
// TypeScript file's types, put the result through the parser bridge, and
// run the document on the tarski evaluator.
//
// It is a module of its own so that the fixture comparison against Node
// (`tests/exe-fixtures.test.ts`) can drive the same pipeline the command
// drives without going through argv, a tsconfig, or a run directory.

import { mkdirSync, writeFileSync } from "node:fs";
import * as path from "node:path";
import ts from "typescript";
import { parseScript } from "../tarski/frontend/src/estree.js";
import {
  type BinaryResult,
  ensureBinary,
  runDocument,
  type SpawnOutcome,
} from "../tarski/frontend/src/binary.js";
import { findTarskiRoot } from "../tarski/frontend/src/test262/paths.js";

/** The `"use strict";` directive `exe` guarantees. */
const STRICT_DIRECTIVE = '"use strict";\n';

/** A leading `"use strict"` the emitted text already carries. */
const ALREADY_STRICT = /^\s*(["'])use strict\1\s*;/;

/**
 * Drop the module syntax tsc emits, in the printer's own AST.
 *
 * `transpileModule` under `module: ESNext` keeps `export` where it found
 * it, and a *before* transformer that removed it would make tsc re-mark
 * the file a module and append `export {};`. An *after* transformer runs
 * past that decision, so what it leaves is plain script text.
 *
 * An `import` declaration is deliberately **left in place**: `exe`
 * resolves no module graph, and the bridge refusing an `ImportDeclaration`
 * by name is a better message than a silently dropped binding.
 */
const stripModuleSyntax: ts.TransformerFactory<ts.SourceFile> = (context) => {
  const { factory } = context;
  const withoutExport = (
    modifiers: readonly ts.ModifierLike[] | undefined,
  ): ts.ModifierLike[] | undefined =>
    modifiers?.filter(
      (m) =>
        m.kind !== ts.SyntaxKind.ExportKeyword &&
        m.kind !== ts.SyntaxKind.DefaultKeyword,
    );
  return (source) => {
    const statements: ts.Statement[] = [];
    for (const statement of source.statements) {
      // `export { a }`, `export * from "./x.js"`: no runtime effect here.
      if (ts.isExportDeclaration(statement)) continue;
      // `export default <expr>` is the expression, evaluated in place.
      if (ts.isExportAssignment(statement)) {
        statements.push(
          factory.createExpressionStatement(statement.expression),
        );
        continue;
      }
      if (ts.isFunctionDeclaration(statement)) {
        statements.push(
          factory.updateFunctionDeclaration(
            statement,
            withoutExport(statement.modifiers),
            statement.asteriskToken,
            statement.name,
            statement.typeParameters,
            statement.parameters,
            statement.type,
            statement.body,
          ),
        );
        continue;
      }
      if (ts.isClassDeclaration(statement)) {
        statements.push(
          factory.updateClassDeclaration(
            statement,
            withoutExport(statement.modifiers),
            statement.name,
            statement.typeParameters,
            statement.heritageClauses,
            statement.members,
          ),
        );
        continue;
      }
      if (ts.isVariableStatement(statement)) {
        statements.push(
          factory.updateVariableStatement(
            statement,
            withoutExport(statement.modifiers) as ts.Modifier[] | undefined,
            statement.declarationList,
          ),
        );
        continue;
      }
      statements.push(statement);
    }
    return factory.updateSourceFile(source, statements);
  };
};

/**
 * A TypeScript file as the script the evaluator runs: types erased by
 * tsc's transpile step, module syntax removed, and `"use strict";` on
 * top.
 *
 * The directive is prepended here rather than left to tsc: under
 * `module: ESNext` tsc emits none for a module even with `alwaysStrict`,
 * and the evaluator's decoder requires the first statement to be that
 * directive — the epic is strict-mode only.
 */
export function stripTypes(source: string, fileName: string): string {
  const { outputText } = ts.transpileModule(source, {
    compilerOptions: {
      target: ts.ScriptTarget.ES2023,
      module: ts.ModuleKind.ESNext,
    },
    fileName,
    transformers: { after: [stripModuleSyntax] },
  });
  return ALREADY_STRICT.test(outputText)
    ? outputText
    : STRICT_DIRECTIVE + outputText;
}

export type ExeOutcome =
  /** The evaluator ran the program: 0, or 1 for an uncaught throw. */
  | { kind: "ran"; status: 0 | 1; stdout: string; stderr: string }
  /** The program spells something the evaluator does not know. */
  | { kind: "unsupported"; node: string }
  /** The evaluator refused the document the bridge handed it. */
  | { kind: "refused"; stderr: string }
  /** There is no evaluator here to run. */
  | { kind: "no-project"; message: string }
  /** `lake build tarski` failed. */
  | { kind: "build-failed"; stdout: string; stderr: string };

/** The binary, injected so the CLI tests can stand in for it. */
export interface ExeDeps {
  ensureBinary: () => BinaryResult;
  runDocument: (binary: string, documentPath: string) => SpawnOutcome;
}

const REAL: ExeDeps = {
  ensureBinary: () => ensureBinary(findTarskiRoot()),
  runDocument: (binary, documentPath) => runDocument(binary, documentPath),
};

/** `unsupported: <Kind>` on the binary's stderr, as `Decode.lean` writes
 * it. Without the marker the whole first line is the best report there
 * is, which is what the test262 runner does with the same stream. */
function unsupportedNode(stderr: string): string {
  /* v8 ignore next 2 -- `split` always yields at least one element; the
     fallback is `noUncheckedIndexedAccess` asking. */
  const line = stderr.split("\n")[0] ?? "";
  const marker = "unsupported: ";
  const at = line.indexOf(marker);
  return at === -1 ? line : line.slice(at + marker.length);
}

/**
 * One source text, run. `outDir` receives the two artifacts — the
 * stripped script and the ESTree document — which are what a user reads
 * when the evaluator refuses something.
 */
export function executeSource(
  source: string,
  fileName: string,
  outDir: string,
  deps: ExeDeps = REAL,
): ExeOutcome {
  const script = stripTypes(source, fileName);
  // A ParseError here would mean tsc's printer emitted text tsc's own
  // parser refuses: an internal bug, not a user error, so it throws.
  const program = parseScript(script, fileName);

  mkdirSync(outDir, { recursive: true });
  const base = path.basename(fileName).replace(/\.[cm]?tsx?$/, "");
  const scriptPath = path.join(outDir, `${base}.js`);
  const documentPath = path.join(outDir, `${base}.json`);
  writeFileSync(scriptPath, script);
  writeFileSync(documentPath, `${JSON.stringify(program, null, 2)}\n`);

  const binary = deps.ensureBinary();
  if (binary.kind === "no-project") return binary;
  if (binary.kind === "failed")
    return {
      kind: "build-failed",
      stdout: binary.stdout,
      stderr: binary.stderr,
    };

  const run = deps.runDocument(binary.binary, documentPath);
  // A spawn that never started — a binary that is not there — answers
  // with both streams null and an error, so neither is assumed.
  const stdout = run.stdout ?? "";
  const stderr =
    (run.stderr ?? "") + (run.error ? `${String(run.error)}\n` : "");
  if (run.status === 0 || run.status === 1)
    return { kind: "ran", status: run.status, stdout, stderr };
  if (run.status === 3)
    return { kind: "unsupported", node: unsupportedNode(stderr) };
  // Status 2, a signal, or a spawn error. The document is the bridge's
  // own output, so a refusal here is a seam bug worth seeing whole.
  return { kind: "refused", stderr };
}
