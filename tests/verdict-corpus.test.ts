import { afterEach, describe, it, expect, vi } from "vitest";
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
  countersatisfiable: "CounterSatisfiable",
  gaveup: "GaveUp",
  nottried: "NotTried",
  inappropriate: "Inappropriate",
  timeout: "Timeout",
};

/** The entry file of every fixture in the corpus, as bucket-relative posix
 * paths. A fixture is one `.ts` file, or a directory whose `main.ts` is the
 * entry of a multi-file closure: the modules it imports are that entry's,
 * not fixtures of their own, and are never run as entries. */
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
      if (entry.isDirectory()) {
        const main = path.join(corpusRoot, bucket, entry.name, "main.ts");
        if (!fs.existsSync(main)) {
          throw new Error(
            `multi-file fixture needs a main.ts entry: ${bucket}/${entry.name}`,
          );
        }
        fixtures.push(`${bucket}/${entry.name}/main.ts`);
        continue;
      }
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

/** The bucket a fixture's verdict is graded against. */
function bucketOf(fixture: string): string | undefined {
  return BUCKET_STATUS[fixture.split("/")[0]!];
}

/** How many `@ensures` a fixture's entry file carries. Every one of them
 * must be graded: the per-file coverage check alone would pass an extractor
 * that silently read fewer blocks than were written. */
function ensuresCount(fixture: string): number {
  const src = fs.readFileSync(path.join(corpusRoot, fixture), "utf8");
  return (src.match(/@ensures\b/g) ?? []).length;
}

// Collected at module scope so the bucket and stray-entry checks fail every
// suite run, Lean or not, and the fixture count can size the test timeout.
const fixtures = corpusFixtures();

// The timeout bucket runs as its own prove invocation under a reduced
// heartbeat budget; everything else runs at the default budget.
const timeoutFixtures = fixtures.filter((f) => f.startsWith("timeout/"));
const mainFixtures = fixtures.filter((f) => !f.startsWith("timeout/"));

// The corpus runs in ONE prove invocation: one Lean build for the whole
// corpus, with per-file containment already localizing artifact failures.
describe.runIf(enabled)("verdict corpus", () => {
  // The budget is per-test state, never ambient: an exported
  // LAKATOS_PROVE_HEARTBEATS would otherwise flip theorem fixtures to
  // Timeout and blame the fixtures. stubEnv restores what was there.
  afterEach(() => {
    vi.unstubAllEnvs();
  });

  useRepoScratchDir(
    path.join(repoRoot, ".lakatos", "verdict-corpus-work"),
    (dir) => {
      // The whole tree, not just the entries: a multi-file fixture's
      // dependencies must sit beside its entry for the import to resolve.
      fs.cpSync(corpusRoot, dir, {
        recursive: true,
        filter: (src) => !src.endsWith("README.md"),
      });
    },
  );

  it(
    "every annotation receives its bucket's SZS status",
    { timeout: proveTimeoutMs(mainFixtures.length) },
    async () => {
      // These fixtures are graded at the default budget; only the timeout
      // bucket reduces it.
      vi.stubEnv("LAKATOS_PROVE_HEARTBEATS", undefined);
      // The countersatisfiable bucket guarantees refutations: exit 1.
      const env = await runForEnvelope(["prove", ...mainFixtures], 1);

      // Completeness: every fixture contributes at least one annotation.
      const covered = new Set(env.annotations.map((a) => a.file));
      expect(mainFixtures.filter((f) => !covered.has(f))).toEqual([]);

      // Completeness, per annotation: a fixture that carries two @ensures
      // contributes two graded entries, however its blocks are divided.
      const graded = new Map<string, number>();
      for (const a of env.annotations) {
        graded.set(a.file, (graded.get(a.file) ?? 0) + 1);
      }
      const undercounted = mainFixtures.flatMap((f) => {
        const want = ensuresCount(f);
        const got = graded.get(f) ?? 0;
        return got === want
          ? []
          : [`${f}: ${want} @ensures written, ${got} graded`];
      });
      expect(undercounted).toEqual([]);

      // One readable diff over ALL mismatches, not just the first.
      const mismatches = env.annotations.flatMap((a) => {
        const want = bucketOf(a.file);
        if (a.szs === want) return [];
        return [
          `${a.file} ${a.function}/${a.property}: expected ${want}, got ${a.szs}`,
        ];
      });
      expect(mismatches).toEqual([]);
    },
  );

  it(
    "timeout fixtures exceed a reduced heartbeat budget",
    { timeout: proveTimeoutMs(timeoutFixtures.length) },
    async () => {
      // The reduced budget is what makes Timeout deterministic: the
      // fixtures are ordinary annotations, not CI-grinding pathologies.
      vi.stubEnv("LAKATOS_PROVE_HEARTBEATS", "1");
      const env = await runForEnvelope(["prove", ...timeoutFixtures], 0);
      const covered = new Set(env.annotations.map((a) => a.file));
      expect(timeoutFixtures.filter((f) => !covered.has(f))).toEqual([]);
      for (const a of env.annotations) {
        expect(a.szs, `${a.file} ${a.function}/${a.property}`).toBe("Timeout");
      }
    },
  );
});
