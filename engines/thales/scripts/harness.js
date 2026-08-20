// Shared scaffolding for the engine's check scripts: where the engine and
// its built frontend live, failure collection, and the exit protocol.

import * as path from 'node:path';
import { fileURLToPath } from 'node:url';

export const engineRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);
export const repoRoot = path.resolve(engineRoot, '..', '..');

/** Import a compiled frontend module: the checks exercise the code the CLI
 * ships, not a copy of it, so they need the root build. */
export async function frontend(module) {
  const built = path.join(
    repoRoot,
    'dist',
    'engines',
    'thales',
    'frontend',
    'src',
    `${module}.js`,
  );
  try {
    return await import(built);
  } catch (e) {
    if (e?.code !== 'ERR_MODULE_NOT_FOUND') throw e;
    console.error(
      `${path.relative(repoRoot, built)} is missing: build the front end first (npx tsc -p tsconfig.json from the repo root)`,
    );
    process.exit(1);
  }
}

/** Collects failures rather than throwing, so one run surfaces every
 * violation instead of stopping at the first. */
export function checker(label) {
  const failures = [];
  return {
    check(cond, message) {
      if (!cond) failures.push(message);
    },
    done(summary) {
      if (failures.length > 0) {
        console.error(`${label} check FAILED:`);
        for (const f of failures) console.error(`  - ${f}`);
        process.exit(1);
      }
      console.log(`${label} check passed (${summary})`);
    },
  };
}
