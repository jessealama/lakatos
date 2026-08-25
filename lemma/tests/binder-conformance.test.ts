import { describe, expect, test } from "vitest";
import { readdirSync, readFileSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { extractFromSource } from "../src/extract.js";
import { parsePrefix } from "../src/prefix-parser.js";
import { resolveClassBinders } from "../src/class-domain.js";
import { isClassDomain } from "../src/domains.js";
import { LemmaError } from "../src/errors.js";

const FIXTURES = path.join(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "..",
  "spec",
  "fixtures",
  "binder",
);

function fixtures(dir: string): Array<[string, string]> {
  const root = path.join(FIXTURES, dir);
  return readdirSync(root)
    .filter((f) => f.endsWith(".ts"))
    .sort()
    .map((f) => [f, readFileSync(path.join(root, f), "utf8")]);
}

describe("spec/fixtures/binder conformance corpus", () => {
  const accept = fixtures("accept");
  const reject = fixtures("reject");

  // Guard against the corpus silently going missing (e.g. a bad path after
  // a directory move): empty directories would vacuously pass.
  test("corpus is present", () => {
    expect(accept.length).toBeGreaterThan(0);
    expect(reject.length).toBeGreaterThan(0);
  });

  // Membership is the expectation (spec/fixtures/README.md): an accepted
  // module's one annotation parses and resolves with no diagnostic, and
  // resolution equips every class binder with its constructor parameters.
  describe("accepts every accept/ fixture", () => {
    for (const [name, src] of accept) {
      test(name, () => {
        const r = extractFromSource(src, name);
        expect(r.invalid).toEqual([]);
        expect(r.annotations).toHaveLength(1);
        const { binders } = parsePrefix(r.annotations[0]!.formula);
        resolveClassBinders(binders, r.classes, name);
        for (const b of binders) {
          if (isClassDomain(b.domain)) {
            expect(b.domain.ctorParams).toBeDefined();
          }
        }
      });
    }
  });

  describe("rejects every reject/ fixture", () => {
    for (const [name, src] of reject) {
      test(name, () => {
        const r = extractFromSource(src, name);
        expect(r.invalid).toEqual([]);
        expect(r.annotations).toHaveLength(1);
        expect(() => {
          const { binders } = parsePrefix(r.annotations[0]!.formula);
          resolveClassBinders(binders, r.classes, name);
        }).toThrow(LemmaError);
      });
    }
  });
});
