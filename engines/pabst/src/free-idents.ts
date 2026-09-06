import { LemmaError } from "../../../lemma/src/index.js";

export const GLOBALS = new Set<string>([
  "Math",
  "Number",
  "JSON",
  "Object",
  "Array",
  "String",
  "Boolean",
  "BigInt",
  "Date",
  "isNaN",
  "isFinite",
  "parseInt",
  "parseFloat",
  "undefined",
  "NaN",
  "Infinity",
  "Symbol",
  "Map",
  "Set",
  "RegExp",
  "Error",
  "console",
]);

export interface Classification {
  freeExports: string[];
}

export function classify(
  idents: Set<string>,
  boundVars: Set<string>,
  moduleExports: Set<string>,
): Classification {
  const freeExports: string[] = [];
  for (const id of idents) {
    if (boundVars.has(id)) continue;
    if (GLOBALS.has(id)) continue;
    if (moduleExports.has(id)) {
      freeExports.push(id);
      continue;
    }
    // The per-annotation wrapper in build-spec prefixes file, line, and
    // property name, so naming them here would state them twice.
    throw new LemmaError(`references '${id}', which is not exported`);
  }
  return { freeExports: [...new Set(freeExports)] };
}
