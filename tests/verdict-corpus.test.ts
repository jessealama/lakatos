import { describe, it, expect } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import {
  proveTimeoutMs,
  runForEnvelope,
  useRepoScratchDir,
} from "./helpers/cli.js";

// Needs the Lean toolchain and is minutes-slow, so it only runs when asked:
// thales.yml sets the variable; unit and coverage runs stay identical
// everywhere by never running it implicitly.
const enabled = process.env.LAKATOS_PROVE_E2E === "1";

const repoRoot = process.cwd();
const corpusRoot = path.join(
  repoRoot,
  "engines",
  "thales",
  "tests",
  "conformance",
);

// Bucket name → the status every annotation in that bucket must receive.
// This table is also the complete list of known buckets, so a stray
// directory in the corpus fails loudly instead of being skipped.
const BUCKET_STATUS: Record<string, string> = {
  theorem: "Theorem",
  gaveup: "GaveUp",
  inappropriate: "Inappropriate",
};

/** Every fixture in the corpus, as bucket-relative posix paths. */
function corpusFixtures(): string[] {
  const fixtures: string[] = [];
  for (const dirent of fs.readdirSync(corpusRoot, { withFileTypes: true })) {
    if (!dirent.isDirectory()) continue; // the README sits beside the buckets
    const bucket = dirent.name;
    if (BUCKET_STATUS[bucket] === undefined) {
      throw new Error(`unknown corpus bucket: ${bucket}`);
    }
    const entries = fs.readdirSync(path.join(corpusRoot, bucket), {
      withFileTypes: true,
    });
    for (const entry of entries) {
      if (entry.name.startsWith(".")) continue; // editor/OS droppings
      if (!entry.isFile() || !entry.name.endsWith(".ts")) {
        throw new Error(
          `stray corpus entry (buckets hold only .ts fixtures): ${bucket}/${entry.name}`,
        );
      }
      fixtures.push(`${bucket}/${entry.name}`);
    }
  }
  return fixtures.sort();
}

// Collected at module scope so the bucket and stray-entry checks fail every
// suite run, Lean or not, and the fixture count can size the test timeout.
const fixtures = corpusFixtures();

// The corpus runs in ONE prove invocation: one Lean build for the whole
// corpus, with per-file containment already localizing artifact failures.
describe.runIf(enabled)("verdict corpus", () => {
  useRepoScratchDir(
    path.join(repoRoot, ".thales", "verdict-corpus-work"),
    (dir) => {
      for (const f of fixtures) {
        const dest = path.join(dir, f);
        fs.mkdirSync(path.dirname(dest), { recursive: true });
        fs.copyFileSync(path.join(corpusRoot, f), dest);
      }
    },
  );

  it(
    "every annotation receives its bucket's SZS status",
    { timeout: proveTimeoutMs(fixtures.length) },
    () => {
      const env = runForEnvelope(["prove", ...fixtures]);

      // Completeness: every fixture contributes at least one annotation.
      const covered = new Set(env.annotations.map((a) => a.file));
      expect(fixtures.filter((f) => !covered.has(f))).toEqual([]);

      // One readable diff over ALL mismatches, not just the first.
      const mismatches = env.annotations.flatMap((a) => {
        const want = BUCKET_STATUS[path.dirname(a.file)];
        if (a.szs === want) return [];
        return [
          `${a.file} ${a.function}/${a.property}: expected ${want}, got ${a.szs}`,
        ];
      });
      expect(mismatches).toEqual([]);
    },
  );
});
