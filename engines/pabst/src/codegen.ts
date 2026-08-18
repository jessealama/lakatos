import * as fs from "node:fs";
import * as path from "node:path";
import { buildSpecs } from "./build-spec.js";
import type { InvalidAnnotation } from "../../../lemma/src/extract.js";
import { emit } from "./emit.js";
import { mirrorPath } from "../../../lemma/src/mirror.js";
import { qualifiedName } from "../../../lemma/src/qualified-name.js";
import { randomSeed } from "./seed.js";

export interface GeneratedProperty {
  function: string;
  property: string;
}

export interface GenResult {
  sourceFile: string;
  /** Absent when the file yielded no runnable specs (only input errors). */
  outFile?: string;
  properties: GeneratedProperty[];
  /** Extraction-level input errors, reported per annotation (InputError). */
  invalid: InvalidAnnotation[];
}

export function generate(
  files: string[],
  outRoot = ".pabst",
  seed: number = randomSeed(),
): GenResult[] {
  const results: GenResult[] = [];
  for (const file of files) {
    // Mirroring shared with thales; the outside-cwd guard fires here even
    // for files that turn out to have nothing to generate.
    const outFile = mirrorPath(file, outRoot, ".pabst.test.ts");
    const { specs, invalid } = buildSpecs(file);
    if (specs.length === 0 && invalid.length === 0) continue;
    if (specs.length === 0) {
      results.push({ sourceFile: file, properties: [], invalid });
      continue;
    }
    fs.mkdirSync(path.dirname(outFile), { recursive: true });
    fs.writeFileSync(outFile, emit(specs, file, outFile, seed), "utf8");
    results.push({
      sourceFile: file,
      outFile,
      properties: specs.map((s) => ({
        function: qualifiedName(s.functionName, s.className, s.isStatic),
        property: s.name,
      })),
      invalid,
    });
  }
  return results;
}
