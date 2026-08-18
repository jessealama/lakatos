import * as path from "node:path";
import { LemmaError } from "./errors.js";

/**
 * The out-file mirroring both engines share: `file`'s cwd-relative path
 * under `outRoot`, with `suffix` appended to the FULL name — the source
 * extension stays, so files differing only by extension cannot collide.
 * A ".."-led (or cross-drive absolute) rel would land the artifact
 * outside outRoot; refuse rather than scatter files.
 */
export function mirrorPath(
  file: string,
  outRoot: string,
  suffix: string,
): string {
  const rel = path.relative(process.cwd(), path.resolve(file));
  if (rel === ".." || rel.startsWith(`..${path.sep}`) || path.isAbsolute(rel)) {
    throw new LemmaError(
      `${file} is outside the current directory; run lakatos from the directory containing it`,
    );
  }
  return path.join(outRoot, rel + suffix);
}
