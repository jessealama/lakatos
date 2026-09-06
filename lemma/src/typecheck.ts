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

/** The gate's program, kept so island typing can build an equivalent
 * one over it: `rootNames` and `options` describe the program, `cwd`
 * locates the cwd-relative file names extraction reports. `options`
 * omits the incremental flags, which belong to the gate's cache alone. */
export interface CheckedProgram {
  program: ts.Program;
  rootNames: string[];
  options: ts.CompilerOptions;
  cwd: string;
}

/** Missing means there is no tsconfig.json, so no options to check under;
 * lakatos refuses to run rather than invent them. Clean carries the
 * program's cwd-relative files so the caller can tell which named files
 * the check never saw. */
export type TypecheckResult =
  | { kind: "missing" }
  | { kind: "clean"; programFiles: string[]; checked?: CheckedProgram }
  | { kind: "failed"; diagnostics: TypecheckDiagnostic[] };

/** Options lakatos requires whatever the project sets. Each protects a
 * model assumption: without strictNullChecks a `number` may hold undefined
 * and the model proves away a NaN; without noImplicitAny an untyped callee
 * flows into a modeled body. The individual flags are forced because tsc
 * lets `strictNullChecks: false` override `strict: true`. */
export const REQUIRED_OPTIONS: ts.CompilerOptions = {
  strict: true,
  strictNullChecks: true,
  noImplicitAny: true,
};

// The version-skew codes discovery already ignores: an option newer than
// the bundled TypeScript cannot make the user's program ill-typed.
export const OPTION_SKEW_ERRORS = new Set([5023, 5024, 5025, 6046]);

/**
 * Type check the program ./tsconfig.json describes, under the user's own
 * compilerOptions with lakatos's required options forced on top.
 * skipLibCheck keeps dependency declarations out of the verdict without
 * weakening checking of the user's code. Given tsBuildInfoFile, the check
 * reads and writes that build-info file so an unchanged project re-checks
 * cheaply.
 */
export function typecheckProject(
  cwd: string,
  tsBuildInfoFile?: string,
): TypecheckResult {
  const parsed = parsedTsconfig(cwd);
  if (parsed === undefined) return { kind: "missing" };
  const programFiles = parsed.fileNames.map((f) => path.relative(cwd, f));
  if (parsed.fileNames.length === 0) return { kind: "clean", programFiles };
  const base: ts.CompilerOptions = {
    ...parsed.options,
    ...REQUIRED_OPTIONS,
    noEmit: true,
    skipLibCheck: true,
  };
  const options: ts.CompilerOptions = {
    ...base,
    ...(tsBuildInfoFile !== undefined
      ? { incremental: true, tsBuildInfoFile }
      : {}),
  };
  let program: ts.Program;
  let diagnostics: readonly ts.Diagnostic[];
  if (tsBuildInfoFile !== undefined) {
    mkdirSync(path.dirname(tsBuildInfoFile), { recursive: true });
    const builder = ts.createIncrementalProgram({
      rootNames: parsed.fileNames,
      options,
    });
    program = builder.getProgram();
    diagnostics = ts.getPreEmitDiagnostics(program);
    // The build-info write is the one emit a noEmit incremental program does.
    builder.emit();
  } else {
    program = ts.createProgram(parsed.fileNames, options);
    diagnostics = ts.getPreEmitDiagnostics(program);
  }
  const errors = diagnostics
    .filter((d) => d.category === ts.DiagnosticCategory.Error)
    .filter((d) => !OPTION_SKEW_ERRORS.has(d.code));
  if (errors.length === 0)
    return {
      kind: "clean",
      programFiles,
      checked: { program, rootNames: parsed.fileNames, options: base, cwd },
    };
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
