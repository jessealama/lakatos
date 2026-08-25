import { mkdirSync } from "node:fs";
import * as path from "node:path";
import { LemmaError } from "../lemma/src/index.js";

/** The root every run's artifacts land under, one directory per invocation. */
export const RUN_ROOT = ".lakatos";

/**
 * Where one invocation's artifacts go, named by the instant the envelope
 * reports as `startedAt` so a report and its artifacts match by eye.
 * Colons are illegal in Windows paths, so the name spells them as hyphens;
 * the rest of the ISO string is kept, which keeps runs sortable and keeps
 * two runs a millisecond apart in separate directories.
 */
export function runDirFor(startedAt: string): string {
  return path.join(RUN_ROOT, startedAt.replaceAll(":", "-"));
}

/** How many names to try before concluding something is wrong with the
 * run root rather than with this one name. */
const MAX_CLAIM_ATTEMPTS = 1000;

/**
 * This invocation's run directory, created here so the name is reserved
 * rather than merely observed free: no run is ever written on top of
 * another's artifacts. Two invocations starting in the same millisecond want
 * the same name — ordinary in a shell loop — so an occupied one is stepped
 * over, not fought for, and the caller reports whichever name it got back.
 */
export function claimRunDir(startedAt: string): string {
  const base = runDirFor(startedAt);
  mkdirSync(RUN_ROOT, { recursive: true });
  for (let n = 1; n <= MAX_CLAIM_ATTEMPTS; n++) {
    const dir = n === 1 ? base : `${base}-${n}`;
    try {
      // Non-recursive on purpose: EEXIST is what makes the claim atomic,
      // where checking first and creating after would race.
      mkdirSync(dir);
      return dir;
    } catch (e) {
      if ((e as NodeJS.ErrnoException).code !== "EEXIST") throw e;
    }
  }
  throw new LemmaError(
    `${base}: no free run directory after ${MAX_CLAIM_ATTEMPTS} attempts`,
  );
}
