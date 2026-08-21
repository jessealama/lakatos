import * as fs from 'node:fs';
import * as path from 'node:path';
import {
  type InvalidAnnotation,
  mirrorPath,
  type RawAnnotation,
} from '../../../../lemma/src/index.js';
import { transcribe, type UntriedAnnotation } from './transcribe.js';

export interface FileArtifact {
  sourceFile: string;
  /** Absent when the file has no valid annotations: nothing to prove. */
  outFile?: string;
  annotations: RawAnnotation[];
  invalid: InvalidAnnotation[];
  untried: UntriedAnnotation[];
}

/** Transcribe each source file into `outRoot`, via the mirroring shared
 * with pabst's codegen. Files with no valid annotations contribute no
 * verdicts, so no artifact is written for them. */
export function writeArtifacts(
  files: string[],
  outRoot = '.thales',
): FileArtifact[] {
  return files.map((file) => {
    const outFile = mirrorPath(file, outRoot, '.lean');
    const { lean, annotations, invalid, untried } = transcribe(
      fs.readFileSync(file, 'utf8'),
      file,
    );
    if (annotations.length === 0) {
      return { sourceFile: file, annotations, invalid, untried };
    }
    fs.mkdirSync(path.dirname(outFile), { recursive: true });
    fs.writeFileSync(outFile, lean, 'utf8');
    return { sourceFile: file, outFile, annotations, invalid, untried };
  });
}
