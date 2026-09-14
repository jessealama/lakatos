// A TypeScript file as the script the parser bridge parses: types erased
// by tsc's transpile step, module syntax removed, and `"use strict";` on
// top.
//
// Two callers hand the bridge the same text. `lakatos exe` runs the
// document on the evaluator; thales's emitter attaches a declaration's
// closure to its emission, so the artifact's AST is what the evaluator
// would run. It lives here because an engine may depend on `tarski/` and
// not on `src/`, and because one function should have one home.

import ts from "typescript";

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
