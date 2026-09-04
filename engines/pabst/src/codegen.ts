import * as fs from "node:fs";
import * as path from "node:path";
import { buildSpecs } from "./build-spec.js";
import {
  type InvalidAnnotation,
  mirrorPath,
  qualifiedName,
} from "../../../lemma/src/index.js";
import { emit } from "./emit.js";
import { randomSeed } from "./seed.js";

export interface GeneratedProperty {
  function: string;
  property: string;
  /** Present when the refuter walks the whole domain: the tuple count. */
  cases?: number;
}

/** An annotation no test was generated for, and why. */
export interface UntriedProperty extends GeneratedProperty {
  reason: string;
}

export interface GenResult {
  sourceFile: string;
  /** Absent when the file yielded no runnable specs (only input errors
   * or refusals). */
  outFile?: string;
  properties: GeneratedProperty[];
  /** Extraction-level input errors, reported per annotation (InputError). */
  invalid: InvalidAnnotation[];
  /** Annotations refused for an unrepresentable domain (NotTried). */
  untried: UntriedProperty[];
}

export function generate(
  files: string[],
  outRoot: string,
  seed: number = randomSeed(),
): GenResult[] {
  const results: GenResult[] = [];
  for (const file of files) {
    // Mirroring shared with thales; the outside-cwd guard fires here even
    // for files that turn out to have nothing to generate.
    const outFile = mirrorPath(file, outRoot, ".pabst.test.ts");
    const { specs, invalid, untried } = buildSpecs(file);
    const refused = untried.map((u) => ({
      function: qualifiedName(u.functionName, u.className, u.isStatic),
      property: u.name,
      reason: u.reason,
    }));
    if (specs.length === 0 && invalid.length === 0 && refused.length === 0)
      continue;
    // Nothing runnable: the file still reports, but no artifact is written
    // and the run never touches it.
    if (specs.length === 0) {
      results.push({
        sourceFile: file,
        properties: [],
        invalid,
        untried: refused,
      });
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
        ...(s.cases !== undefined ? { cases: s.cases } : {}),
      })),
      invalid,
      untried: refused,
    });
  }
  return results;
}
