// Where the runner's pieces are, given only where this module is.
//
// The lake package is found by walking up from this file, the way thales's
// `findEngineRoot` finds its own: an installed copy and a checkout put
// `dist/` in different places, and neither can be named relative to the
// other.

import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

/**
 * The `tarski/` lake package: the nearest ancestor that either holds a
 * `tarski/lakefile.lean` or is one itself.
 */
export function findTarskiRoot(
  from: string = fileURLToPath(import.meta.url),
): string | undefined {
  let dir = path.dirname(from);
  for (;;) {
    for (const candidate of [dir, path.join(dir, "tarski")]) {
      if (existsSync(path.join(candidate, "lakefile.lean"))) return candidate;
    }
    const parent = path.dirname(dir);
    if (parent === dir) return undefined;
    dir = parent;
  }
}

/** Where `lake build tarski` puts the binary. */
export function defaultBinary(root: string): string {
  return path.join(root, ".lake", "build", "bin", "tarski");
}

/**
 * The test262 checkout: `LAKATOS_TEST262` when it is set, and the ignored
 * clone the setup command makes otherwise.
 */
export function defaultCheckout(root: string): string {
  return process.env.LAKATOS_TEST262 ?? path.join(root, ".test262");
}

/** The pinned commit the setup command clones. */
export function pinPath(root: string): string {
  return path.join(root, "test262", "pin.json");
}
