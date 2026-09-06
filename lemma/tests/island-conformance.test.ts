import { describe, expect, test, beforeAll, afterAll } from "vitest";
import {
  cpSync,
  mkdtempSync,
  readdirSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { extract } from "../src/extract.js";
import { parsePrefix } from "../src/prefix-parser.js";
import { parseBody } from "../src/formula-parser.js";
import { typecheckProject } from "../src/typecheck.js";
import {
  typeFormulas,
  type IslandTyping,
  type ParsedFile,
} from "../src/island-types.js";

const CORPUS = path.join(
  path.dirname(fileURLToPath(import.meta.url)),
  "..",
  "..",
  "spec",
  "fixtures",
  "island",
);

// The whole corpus is one program in a scratch directory: island typing
// needs the host's default library and the required options, which a
// tsconfig with no compilerOptions provides once lakatos forces its own.
const TSCONFIG = JSON.stringify({
  compilerOptions: { target: "es2022", module: "nodenext", types: [] },
  include: ["**/*.ts"],
});

function names(dir: string): string[] {
  return readdirSync(path.join(CORPUS, dir))
    .filter((f) => f.endsWith(".ts"))
    .sort();
}

describe("spec/fixtures/island conformance corpus", () => {
  const accept = names("accept");
  const reject = names("reject");
  let dir: string;
  let prevCwd: string;
  const typing = (rel: string): IslandTyping => {
    const check = typecheckProject(dir);
    if (check.kind !== "clean")
      throw new Error(
        `the corpus must type check on its own: ${JSON.stringify(check)}`,
      );
    const r = extract(rel);
    const file: ParsedFile = {
      file: rel,
      exports: r.exports,
      classes: r.classes,
      annotations: r.annotations.map((raw) => {
        const { binders, body } = parsePrefix(raw.formula);
        return { raw, parsed: { binders, formula: parseBody(body) } };
      }),
    };
    expect(r.invalid).toEqual([]);
    expect(r.annotations).toHaveLength(1);
    return typeFormulas([file], check.checked);
  };

  beforeAll(() => {
    dir = mkdtempSync(path.join(os.tmpdir(), "lemma-island-corpus-"));
    cpSync(CORPUS, dir, { recursive: true });
    writeFileSync(path.join(dir, "tsconfig.json"), TSCONFIG, "utf8");
    prevCwd = process.cwd();
    process.chdir(dir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    rmSync(dir, { recursive: true, force: true });
  });

  test("corpus is present", () => {
    expect(accept.length).toBeGreaterThan(0);
    expect(reject.length).toBeGreaterThan(0);
  });

  describe("accepts every accept/ fixture", () => {
    for (const name of accept) {
      test(name, () => {
        expect(typing(path.join("accept", name))).toEqual({
          invalid: [],
          refused: new Set(),
        });
      });
    }
  });

  describe("rejects every reject/ fixture with one diagnostic naming the atom", () => {
    for (const name of reject) {
      test(name, () => {
        const t = typing(path.join("reject", name));
        expect(t.invalid).toHaveLength(1);
        expect(t.invalid[0]!.invalid).toHaveLength(1);
        expect(t.invalid[0]!.invalid[0]!.message).toMatch(/in atom `/);
        expect(t.refused.size).toBe(1);
      });
    }
  });
});
