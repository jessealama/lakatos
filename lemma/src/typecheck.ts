import { mkdirSync } from "node:fs";
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
 * verdict without weakening checking of the user's code. Given
 * tsBuildInfoFile, the check reads and writes that build-info file so an
 * unchanged project re-checks cheaply.
 */
export function typecheckProject(
  cwd: string,
  tsBuildInfoFile?: string,
): TypecheckResult {
  const parsed = parsedTsconfig(cwd);
  if (parsed === undefined) return { kind: "skipped", reason: "no-tsconfig" };
  if (parsed.fileNames.length === 0)
    return { kind: "skipped", reason: "no-inputs" };
  const options: ts.CompilerOptions = {
    ...parsed.options,
    noEmit: true,
    skipLibCheck: true,
    ...(tsBuildInfoFile !== undefined
      ? { incremental: true, tsBuildInfoFile }
      : {}),
  };
  let diagnostics: readonly ts.Diagnostic[];
  if (tsBuildInfoFile !== undefined) {
    mkdirSync(path.dirname(tsBuildInfoFile), { recursive: true });
    const builder = ts.createIncrementalProgram({
      rootNames: parsed.fileNames,
      options,
    });
    diagnostics = ts.getPreEmitDiagnostics(builder.getProgram());
    // The build-info write is the one emit a noEmit incremental program does.
    builder.emit();
  } else {
    const program = ts.createProgram(parsed.fileNames, options);
    diagnostics = ts.getPreEmitDiagnostics(program);
  }
  const errors = diagnostics
    .filter((d) => d.category === ts.DiagnosticCategory.Error)
    .filter((d) => !OPTION_SKEW_ERRORS.has(d.code));
  if (errors.length === 0) return { kind: "clean" };
  return { kind: "failed", diagnostics: errors.map((d) => structured(d, cwd)) };
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
