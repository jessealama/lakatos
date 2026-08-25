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

describe("spec/fixtures/attach conformance corpus", () => {
  const accept = fixtures("accept");
  const reject = fixtures("reject");

  // Guard against the corpus silently going missing (e.g. a bad path after
  // a directory move): empty directories would vacuously pass.
  test("corpus is present", () => {
    expect(accept.length).toBeGreaterThan(0);
    expect(reject.length).toBeGreaterThan(0);
  });

  // Membership is the expectation (spec/fixtures/README.md). Each fixture
  // carries exactly one @ensures, so the two outcomes partition cleanly:
  // an accepted attachment point yields an annotation and no diagnostic.
  describe("accepts every accept/ fixture", () => {
    for (const [name, src] of accept) {
      test(name, () => {
        const r = extractFromSource(src, name);
        expect(r.invalid).toEqual([]);
        expect(r.annotations).toHaveLength(1);
      });
    }
  });

  describe("rejects every reject/ fixture", () => {
    for (const [name, src] of reject) {
      test(name, () => {
        const r = extractFromSource(src, name);
        expect(r.annotations).toEqual([]);
        expect(r.invalid).toHaveLength(1);
      });
    }
  });
});
