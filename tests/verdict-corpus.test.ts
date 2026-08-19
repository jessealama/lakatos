import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import type { Envelope } from "../src/envelope.js";

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
    if (!dirent.isDirectory()) continue;
    const bucket = dirent.name;
    if (BUCKET_STATUS[bucket] === undefined) {
      throw new Error(`unknown corpus bucket: ${bucket}`);
    }
    for (const name of fs.readdirSync(path.join(corpusRoot, bucket)).sort()) {
      if (name.endsWith(".ts")) fixtures.push(`${bucket}/${name}`);
    }
  }
  return fixtures.sort();
}

// The corpus runs inside the repo tree (a gitignored scratch dir) like the
// e2e suite, and in ONE prove invocation: one Lean build for the whole
// corpus, with per-file containment already localizing artifact failures.
describe.runIf(enabled)("verdict corpus", () => {
  const workDir = path.join(repoRoot, ".thales", "verdict-corpus-work");
  let fixtures: string[] = [];

  beforeAll(() => {
    fixtures = corpusFixtures();
    fs.rmSync(workDir, { recursive: true, force: true });
    for (const f of fixtures) {
      const dest = path.join(workDir, f);
      fs.mkdirSync(path.dirname(dest), { recursive: true });
      fs.copyFileSync(path.join(corpusRoot, f), dest);
    }
    process.chdir(workDir);
  });
  afterAll(() => {
    process.chdir(repoRoot);
    fs.rmSync(workDir, { recursive: true, force: true });
  });

  it(
    "every annotation receives its bucket's SZS status",
    { timeout: 600_000 },
    () => {
      const run = runMain(["prove", ...fixtures]);
      expect(run.code, run.stderr.join("\n")).toBe(0);
      expect(run.stdout).toHaveLength(1);
      const env = JSON.parse(run.stdout[0]!) as Envelope;
      expectValidEnvelope(env);

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
