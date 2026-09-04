import * as fs from "node:fs";
import * as path from "node:path";
import {
  type InvalidAnnotation,
  mirrorPath,
  type RawAnnotation,
} from "../../../../lemma/src/index.js";
import { type ClassifiedAnnotation, emitModule } from "./emission.js";

export interface EmissionArtifact {
  sourceFile: string;
  /** Absent when the file has no valid annotations: nothing to prove. */
  jsonFile?: string;
  /** Where thales-emit renders the artifact; set only when at least one
   * obligation reaches Lean. */
  leanFile?: string;
  annotations: RawAnnotation[];
  invalid: InvalidAnnotation[];
  classified: ClassifiedAnnotation[];
}

/** Emit each source file's per-declaration JSON into `outRoot`, via
 * `mirrorPath` — the same source-tree mirroring the run directory uses.
 * The .lean artifact is rendered later by thales-emit, inside the engine
 * run; a file whose annotations are all classified frontend-side never
 * reaches Lean at all. */
export function writeEmissionArtifacts(
  files: string[],
  outRoot: string,
): EmissionArtifact[] {
  return files.map((file) => {
    const { emission, annotations, invalid, classified } = emitModule(
      fs.readFileSync(file, "utf8"),
      file,
    );
    if (annotations.length === 0) {
      return { sourceFile: file, annotations, invalid, classified };
    }
    const jsonFile = mirrorPath(file, outRoot, ".json");
    fs.mkdirSync(path.dirname(jsonFile), { recursive: true });
    fs.writeFileSync(jsonFile, JSON.stringify(emission), "utf8");
    const leanFile =
      emission.obligations.length > 0
        ? mirrorPath(file, outRoot, ".lean")
        : undefined;
    return {
      sourceFile: file,
      jsonFile,
      ...(leanFile !== undefined ? { leanFile } : {}),
      annotations,
      invalid,
      classified,
    };
  });
}
