import * as fs from 'node:fs';
import * as path from 'node:path';
import { LemmaError } from '../../../../lemma/src/errors.js';
import type {
  InvalidAnnotation,
  RawAnnotation,
} from '../../../../lemma/src/extract.js';
import { transcribe } from './transcribe.js';

const SRC_EXT = /\.(ts|tsx|mts|cts|js|mjs|cjs)$/;

export interface FileArtifact {
  sourceFile: string;
  /** Absent when the file has no valid annotations: nothing to prove. */
  outFile?: string;
  annotations: RawAnnotation[];
  invalid: InvalidAnnotation[];
}

/** Transcribe each source file into `outRoot`, mirroring its path (as
 * pabst's codegen does with .pabst/). Files with no valid annotations
 * contribute no verdicts, so no artifact is written for them. */
export function writeArtifacts(
  files: string[],
  outRoot = '.thales',
): FileArtifact[] {
  return files.map((file) => {
    const rel = path.relative(process.cwd(), path.resolve(file));
    // A ".."-led (or cross-drive absolute) rel would land the artifact
    // outside outRoot; refuse rather than scatter files.
    if (
      rel === '..' ||
      rel.startsWith(`..${path.sep}`) ||
      path.isAbsolute(rel)
    ) {
      throw new LemmaError(
        `${file} is outside the current directory; run lakatos from the directory containing it`,
      );
    }
    const { lean, annotations, invalid } = transcribe(
      fs.readFileSync(file, 'utf8'),
      file,
    );
    if (annotations.length === 0) {
      return { sourceFile: file, annotations, invalid };
    }
    const outFile = path.join(outRoot, rel.replace(SRC_EXT, '') + '.lean');
    fs.mkdirSync(path.dirname(outFile), { recursive: true });
    fs.writeFileSync(outFile, lean, 'utf8');
    return { sourceFile: file, outFile, annotations, invalid };
  });
}
