import { describe, it, expect } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import {
  proveTimeoutMs,
  runForEnvelope,
  useRepoScratchDir,
} from "./helpers/cli.js";
import type { Envelope } from "../src/envelope.js";

// Needs the Lean toolchain and is minutes-slow, so it only runs when asked:
// thales.yml sets the variable; unit and coverage runs stay identical
// everywhere by never running it implicitly.
const enabled = process.env.LAKATOS_PROVE_E2E === "1";

const repoRoot = process.cwd();

describe.runIf(enabled)("lakatos prove end-to-end (tracer)", () => {
  useRepoScratchDir(path.join(repoRoot, ".thales", "e2e-work"), (dir) => {
    fs.copyFileSync(
      path.join(
        repoRoot,
        "engines",
        "thales",
        "tests",
        "fixtures",
        "tracer.ts",
      ),
      path.join(dir, "tracer.ts"),
    );
    // The identity-parity check needs a file BOTH engines can process end
    // to end (refute's compile front-end rejects the tracer's deliberately
    // broken constructs), so it reuses the corpus's add-commutes fixture.
    fs.copyFileSync(
      path.join(
        repoRoot,
        "engines",
        "thales",
        "tests",
        "conformance",
        "theorem",
        "add-commutes.ts",
      ),
      path.join(dir, "parity.ts"),
    );
  });

  it(
    "one healthy run: Theorem and Inappropriate per annotation",
    { timeout: proveTimeoutMs(1) },
    () => {
      const env = runForEnvelope(["prove", "tracer.ts"]);

      const by = new Map(
        env.annotations.map((a) => [`${a.function}/${a.property}`, a]),
      );
      expect(by.get("add/commutes")).toMatchObject({ szs: "Theorem" });
      expect(by.get("fetchTotal/nonNegative")).toMatchObject({
        szs: "Inappropriate",
        reason: expect.stringContaining("AwaitExpression"),
      });
      expect(by.get("Counter#bump/bumps")).toMatchObject({
        szs: "Inappropriate",
        reason: expect.stringContaining("ClassDeclaration"),
      });
      expect(env.annotations).toHaveLength(3);
    },
  );

  it(
    "prove and refute report identical identity keys for the same file",
    { timeout: proveTimeoutMs(1) },
    () => {
      const proveEnv = runForEnvelope(["prove", "parity.ts"]);
      expect(proveEnv.annotations[0]).toMatchObject({ szs: "Theorem" });

      const refuteEnv = runForEnvelope(["refute", "parity.ts"]);

      const ids = (e: Envelope) =>
        e.annotations.map((a) => [a.file, a.function, a.property]).sort();
      expect(ids(proveEnv)).toEqual([["parity.ts", "add", "commutes"]]);
      expect(ids(proveEnv)).toEqual(ids(refuteEnv));
    },
  );
});
