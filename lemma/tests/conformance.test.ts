import { describe, expect, test } from "vitest";
import { readdirSync, readFileSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { parsePrefix } from "../src/prefix-parser.js";
import { parseBody } from "../src/formula-parser.js";
import { LemmaError } from "../src/errors.js";

interface Fixture {
  annotation: string;
  note: string;
  stage?: "prefix" | "formula";
}

const FIXTURES = path.join(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "..",
  "spec",
  "fixtures",
);

function fixtures(dir: string): Array<[string, Fixture]> {
  const root = path.join(FIXTURES, dir);
  return readdirSync(root)
    .filter((f) => f.endsWith(".json"))
    .map((f) => [f, JSON.parse(readFileSync(path.join(root, f), "utf8"))]);
}

/** Membership is the expectation (spec/fixtures/README.md): parse both
 * stages and let any throw fail the accept case; a reject case must throw
 * LemmaError from one of them — plain Error would mean a crash, not a
 * diagnostic. */
function parse(annotation: string): void {
  parseBody(parsePrefix(annotation).body);
}

describe("spec/fixtures conformance corpus", () => {
  const accept = fixtures("accept");
  const reject = fixtures("reject");

  // Guard against the corpus silently going missing (e.g. a bad path after
  // a directory move): empty directories would vacuously pass.
  test("corpus is present", () => {
    expect(accept.length).toBeGreaterThan(0);
    expect(reject.length).toBeGreaterThan(0);
  });

  describe("accepts every accept/ fixture", () => {
    for (const [name, fixture] of accept) {
      test(`${name} (${fixture.note})`, () => {
        expect(() => parse(fixture.annotation)).not.toThrow();
      });
    }
  });

  describe("rejects every reject/ fixture", () => {
    for (const [name, fixture] of reject) {
      test(`${name} (${fixture.note})`, () => {
        expect(() => parse(fixture.annotation)).toThrow(LemmaError);
      });
    }
  });
});
