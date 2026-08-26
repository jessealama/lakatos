import { afterAll, beforeAll, describe, expect, test } from "vitest";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { emitModule } from "../src/emission.js";
import { writeEmissionArtifacts } from "../src/emission-artifacts.js";

const OUT = "out";

const ANNOTATED =
  "/** @ensures{q} forall (x: int ∈ [0, 5)) { f(x) === x } */\nexport function f(x: number): number { return x; }\n";

const CLASS_BINDER =
  "export class Box { constructor(readonly size: number) {} }\n" +
  "/** @ensures{p} forall (b: Box) { volume(b) >= 0 } */\n" +
  "export function volume(b: Box): number { return b.size; }\n";

describe("writeEmissionArtifacts", () => {
  let dir: string;
  const prevCwd = process.cwd();
  beforeAll(() => {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), "thales-emission-artifacts-"));
    fs.mkdirSync(path.join(dir, "sub"));
    fs.writeFileSync(path.join(dir, "sub", "a.ts"), ANNOTATED);
    fs.writeFileSync(path.join(dir, "plain.ts"), "export const x = 1;\n");
    fs.writeFileSync(path.join(dir, "boxed.ts"), CLASS_BINDER);
    process.chdir(dir);
  });
  afterAll(() => {
    process.chdir(prevCwd);
    fs.rmSync(dir, { recursive: true, force: true });
  });

  test("writes one emission JSON per annotated file, mirrored", () => {
    const source = path.join("sub", "a.ts");
    const [a] = writeEmissionArtifacts([source], OUT);
    expect(a!.jsonFile).toBe(path.join(OUT, "sub", "a.ts.json"));
    expect(a!.leanFile).toBe(path.join(OUT, "sub", "a.ts.lean"));
    const written = JSON.parse(fs.readFileSync(a!.jsonFile!, "utf8"));
    expect(written).toEqual(emitModule(ANNOTATED, source).emission);
    expect(a!.annotations).toHaveLength(1);
    expect(a!.classified).toEqual([]);
    // The .lean artifact is thales-emit's to render, not the frontend's.
    expect(fs.existsSync(a!.leanFile!)).toBe(false);
  });

  test("an annotation-free file gets an entry but no artifact", () => {
    const [p] = writeEmissionArtifacts(["plain.ts"], OUT);
    expect(p).toEqual({
      sourceFile: "plain.ts",
      annotations: [],
      invalid: [],
      classified: [],
    });
    expect(fs.existsSync(path.join(OUT, "plain.ts.json"))).toBe(false);
  });

  test("a fully classified file keeps its JSON but plans no Lean artifact", () => {
    const [b] = writeEmissionArtifacts(["boxed.ts"], OUT);
    expect(b!.jsonFile).toBe(path.join(OUT, "boxed.ts.json"));
    expect(b!.leanFile).toBeUndefined();
    expect(b!.classified).toHaveLength(1);
    expect(b!.classified[0]!.szs).toBe("Inappropriate");
  });
});
