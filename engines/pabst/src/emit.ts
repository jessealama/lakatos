import * as path from "node:path";
import {
  BOOL_ALIAS,
  BOOL_EXPORT,
  BUDGET_ALIAS,
  BUDGET_EXPORT,
  REPORT_ALIAS,
  REPORT_EXPORT,
  RUNTIME_SPECIFIER,
} from "./contract.js";
import { ctorCall, ctorShape } from "./ctor.js";
import { arbitraryFor } from "./domains.js";
import { emitEnumerated } from "./enumerate.js";
import { isClassDomain, qualifiedName } from "../../../lemma/src/index.js";
import type { PropertySpec } from "./ir.js";

const SRC_EXT = /\.(ts|tsx|mts|cts|js|mjs|cjs)$/;

export function emit(
  specs: PropertySpec[],
  sourceFile: string,
  outFile: string,
  seed: number,
): string {
  const srcAbs = path.resolve(sourceFile).replace(SRC_EXT, "");
  const outDir = path.dirname(path.resolve(outFile));
  let rel = path.relative(outDir, srcAbs).split(path.sep).join("/");
  if (!rel.startsWith(".")) rel = "./" + rel;

  const allExports = [...new Set(specs.flatMap((s) => s.freeExports))].sort();

  const lines: string[] = [];
  lines.push(`import { describe } from "vitest";`);
  lines.push(`import { test, fc } from "@fast-check/vitest";`);
  lines.push(
    `import { ${REPORT_EXPORT} as ${REPORT_ALIAS}, ${BOOL_EXPORT} as ${BOOL_ALIAS}, ${BUDGET_EXPORT} as ${BUDGET_ALIAS} } from "${RUNTIME_SPECIFIER}";`,
  );
  lines.push(`import * as __M from "${rel}";`);
  if (allExports.length > 0)
    lines.push(`const { ${allExports.join(", ")} } = __M;`);
  lines.push("");
  lines.push(`describe("pabst", () => {`);

  // Group by class (undefined = top-level function), then by member name.
  const byClass = new Map<string | undefined, Map<string, PropertySpec[]>>();
  for (const s of specs) {
    let methods = byClass.get(s.className);
    if (!methods) {
      methods = new Map<string, PropertySpec[]>();
      byClass.set(s.className, methods);
    }
    const arr = methods.get(s.functionName) ?? [];
    arr.push(s);
    methods.set(s.functionName, arr);
  }

  for (const [className, methods] of byClass) {
    if (className === undefined) {
      for (const [fnName, fnSpecs] of methods) {
        lines.push(`  describe(${JSON.stringify(fnName)}, () => {`);
        for (const s of fnSpecs)
          lines.push(emitSpec(s, sourceFile, seed, "    "));
        lines.push(`  });`);
      }
    } else {
      lines.push(`  describe(${JSON.stringify(className)}, () => {`);
      for (const [methodName, mSpecs] of methods) {
        lines.push(`    describe(${JSON.stringify(methodName)}, () => {`);
        for (const s of mSpecs)
          lines.push(emitSpec(s, sourceFile, seed, "      "));
        lines.push(`    });`);
      }
      lines.push(`  });`);
    }
  }

  lines.push(`});`);
  lines.push("");
  return lines.join("\n");
}

/** A spec at or under the enumeration cap walks its domain; the rest sample. */
function emitSpec(
  s: PropertySpec,
  sourceFile: string,
  seed: number,
  indent: string,
): string {
  return s.cases === undefined
    ? emitProp(s, sourceFile, seed, indent)
    : emitEnumerated(s, s.cases, sourceFile, indent);
}

function emitProp(
  s: PropertySpec,
  sourceFile: string,
  seed: number,
  indent: string,
): string {
  const arbs = s.binders.map((b) => arbitraryFor(b)).join(", ");
  // A class binder's generated value is its constructor-argument tuple;
  // the instance is constructed in the test body so a throwing tuple can
  // discard the sample (it denotes no instance — spec/semantics.md).
  const shapes = s.binders.map((b) =>
    isClassDomain(b.domain) ? ctorShape(b.domain) : null,
  );
  const vars = s.binders
    .map((b, i) => (shapes[i] === null ? b.varName : `__args_${b.varName}`))
    .join(", ");
  const varNames = s.binders.map((b) => JSON.stringify(b.varName)).join(", ");
  const name = JSON.stringify(s.name);
  const file = JSON.stringify(sourceFile);
  const fn = JSON.stringify(
    qualifiedName(s.functionName, s.className, s.isStatic),
  );
  const hasClass = shapes.some((c) => c !== null);
  const ctors = hasClass
    ? `, [${shapes.map((c) => JSON.stringify(c)).join(", ")}]`
    : "";
  const reporter = `(d) => ${REPORT_ALIAS}(${file}, ${fn}, ${name}, [${varNames}], d${ctors})`;
  const params = `{ seed: ${seed}, reporter: ${reporter} }`;
  const out: string[] = [];
  out.push(`${indent}test.prop([${arbs}], ${params})(${name}, (${vars}) => {`);
  for (const b of s.binders) {
    if (!isClassDomain(b.domain)) continue;
    const v = b.varName;
    const cls = b.domain.className;
    const call = ctorCall(cls, b.domain.ctorParams!, `__args_${v}`);
    out.push(`${indent}  let ${v}!: ${cls};`);
    out.push(`${indent}  try { ${v} = ${call}; } catch { fc.pre(false); }`);
  }
  for (const p of s.preconditions) out.push(`${indent}  fc.pre(${p});`);
  out.push(`${indent}  const __r = (${s.body});`);
  out.push(`${indent}  return __r;`);
  out.push(`${indent}});`);
  return out.join("\n");
}
