import * as path from "node:path";
import ts from "typescript";
import { parsedTsconfig } from "./discover.js";

/** One type-check finding. `file` is cwd-relative and absent for
 * project-level diagnostics; `line` is 1-indexed and travels with it. */
export interface TypecheckDiagnostic {
  file?: string;
  line?: number;
  code: number;
  message: string;
}

/** Skipped means there was nothing to check under the user's own options:
 * no tsconfig at all, or one that names no input files. */
export type TypecheckResult =
  | { kind: "skipped"; reason: "no-tsconfig" | "no-inputs" }
  | { kind: "clean" }
  | { kind: "failed"; diagnostics: TypecheckDiagnostic[] };

// The version-skew codes discovery already ignores: an option newer than
// the bundled TypeScript cannot make the user's program ill-typed.
const OPTION_SKEW_ERRORS = new Set([5023, 5024, 5025, 6046]);

/**
 * Type check the program ./tsconfig.json describes, under the user's own
 * compilerOptions. skipLibCheck keeps dependency declarations out of the
 * verdict without weakening checking of the user's code.
 */
export function typecheckProject(cwd: string): TypecheckResult {
  const parsed = parsedTsconfig(cwd);
  if (parsed === undefined) return { kind: "skipped", reason: "no-tsconfig" };
  if (parsed.fileNames.length === 0)
    return { kind: "skipped", reason: "no-inputs" };
  const options: ts.CompilerOptions = {
    ...parsed.options,
    noEmit: true,
    skipLibCheck: true,
  };
  const program = ts.createProgram(parsed.fileNames, options);
  const diagnostics = ts
    .getPreEmitDiagnostics(program)
    .filter((d) => d.category === ts.DiagnosticCategory.Error)
    .filter((d) => !OPTION_SKEW_ERRORS.has(d.code));
  if (diagnostics.length === 0) return { kind: "clean" };
  return {
    kind: "failed",
    diagnostics: diagnostics.map((d) => structured(d, cwd)),
  };
}

function structured(d: ts.Diagnostic, cwd: string): TypecheckDiagnostic {
  const message = ts.flattenDiagnosticMessageText(d.messageText, " ");
  if (d.file === undefined || d.start === undefined)
    return { code: d.code, message };
  const { line } = d.file.getLineAndCharacterOfPosition(d.start);
  return {
    file: path.relative(cwd, d.file.fileName),
    line: line + 1,
    code: d.code,
    message,
  };
}
