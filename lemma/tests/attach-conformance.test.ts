import { describe, expect, test } from "vitest";
import { readdirSync, readFileSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { extractFromSource } from "../src/extract.js";

const FIXTURES = path.join(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "..",
  "spec",
  "fixtures",
  "attach",
);

function fixtures(dir: string): Array<[string, string]> {
  const root = path.join(FIXTURES, dir);
  return readdirSync(root)
    .filter((f) => f.endsWith(".ts"))
    .sort()
    .map((f) => [f, readFileSync(path.join(root, f), "utf8")]);
}

/** How many `@ensures` a fixture carries. Each one must be accounted for,
 * as an annotation or as a diagnostic: a harness that asked only for "at
 * least one" would pass an extractor that silently read fewer blocks than
 * were written. */
function ensuresCount(src: string): number {
  return (src.match(/@ensures\b/g) ?? []).length;
}

describe("spec/fixtures/attach conformance corpus", () => {
  const accept = fixtures("accept");
  const reject = fixtures("reject");

  // Guard against the corpus silently going missing (e.g. a bad path after
  // a directory move): empty directories would vacuously pass.
  test("corpus is present", () => {
    expect(accept.length).toBeGreaterThan(0);
    expect(reject.length).toBeGreaterThan(0);
  });

  // Membership is the expectation (spec/fixtures/README.md). Every @ensures a
  // fixture carries is accounted for, so the two outcomes partition cleanly:
  // an accepted attachment point yields one annotation per @ensures and no
  // diagnostic.
  describe("accepts every accept/ fixture", () => {
    for (const [name, src] of accept) {
      test(name, () => {
        const r = extractFromSource(src, name);
        expect(r.invalid).toEqual([]);
        expect(ensuresCount(src)).toBeGreaterThan(0);
        expect(r.annotations).toHaveLength(ensuresCount(src));
      });
    }
  });

  describe("rejects every reject/ fixture", () => {
    for (const [name, src] of reject) {
      test(name, () => {
        const r = extractFromSource(src, name);
        expect(r.annotations).toEqual([]);
        expect(ensuresCount(src)).toBeGreaterThan(0);
        expect(r.invalid).toHaveLength(ensuresCount(src));
      });
    }
  });
});
