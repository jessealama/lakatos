import { describe, it, expect } from "vitest";
import { readdirSync, readFileSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

/** Everything outside lemma/ — lemma's own tests may reach for internals. */
const TREES = [
  "src",
  "tests",
  "engines/pabst/src",
  "engines/pabst/tests",
  "engines/thales/frontend/src",
  "engines/thales/frontend/tests",
];

/** Anchored on `from`, so prose and `vi.mock` targets are not hits. Mocking a
 * lemma internal is fine — the seam is narrower than the barrel. */
const FROM_CLAUSE = /\bfrom\s+["']([^"']+)["']/g;
const LEMMA_MODULE = /(?:^|\/)lemma\/src\/(.+)$/;

function tsFiles(tree: string): string[] {
  return readdirSync(path.join(REPO, tree), { recursive: true })
    .map(String)
    .filter((f) => f.endsWith(".ts"))
    .map((f) => path.join(tree, f));
}

describe("lemma's public surface", () => {
  it("is reached only through the barrel", () => {
    const deep: string[] = [];
    for (const tree of TREES) {
      for (const file of tsFiles(tree)) {
        const text = readFileSync(path.join(REPO, file), "utf8");
        for (const [, specifier] of text.matchAll(FROM_CLAUSE)) {
          const tail = LEMMA_MODULE.exec(specifier!)?.[1];
          if (tail !== undefined && tail !== "index.js") {
            deep.push(`${file} -> lemma/src/${tail}`);
          }
        }
      }
    }
    expect(
      deep,
      "these deep-import a lemma internal; import the barrel instead, adding " +
        "the name to it if it belongs in lemma's public surface",
    ).toEqual([]);
  });
});
