import { describe, it, expect } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runForEnvelope, useRepoScratchDir } from "./helpers/cli.js";

const repoRoot = process.cwd();

// A bounded int binder whose clean pass used to report GaveUp.
const SMALL = [
  "/** @ensures{pos} forall (n: int ∈ [1, 10]) { square(n) > 0 } */",
  "export function square(n: number): number { return n * n; }",
  "",
].join("\n");

describe("lakatos refute walks a small domain in full", () => {
  useRepoScratchDir(
    path.join(repoRoot, ".lakatos", "refute-enumerated"),
    (dir) => {
      fs.writeFileSync(path.join(dir, "small.ts"), SMALL, "utf8");
    },
  );

  it(
    "reports Theorem with the case count and exits 0",
    { timeout: 60000 },
    async () => {
      const env = await runForEnvelope(["refute", "small.ts"]);
      expect(env).toMatchObject({ generated: 1, passed: 1, failed: 0 });
      expect(env.annotations).toEqual([
        {
          file: "small.ts",
          function: "square",
          property: "pos",
          szs: "Theorem",
          kind: "enumerated",
          cases: 10,
        },
      ]);
    },
  );
});
