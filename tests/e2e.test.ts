import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { runMain } from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import type { Envelope } from "../src/envelope.js";

// Needs the Lean toolchain and is minutes-slow, so it only runs when asked:
// thales.yml sets the variable; unit and coverage runs stay identical
// everywhere by never running it implicitly.
const enabled = process.env.LAKATOS_PROVE_E2E === "1";

const repoRoot = process.cwd();

// A file BOTH engines can process end to end, for the identity-parity
// check (refute's compile front-end rejects the tracer's deliberately
// broken constructs before it can emit an envelope).
const paritySource = `/** @ensures{commutes} forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) } */
export function add(a: number, b: number): number {
  return a + b;
}
`;

// Refute's generated tests import "lakatos/runtime" via the package
// self-reference, so this suite must run inside the repo tree (a
// gitignored scratch dir), not under os.tmpdir().
describe.runIf(enabled)("lakatos prove end-to-end (tracer)", () => {
  const workDir = path.join(repoRoot, ".thales", "e2e-work");

  beforeAll(() => {
    fs.rmSync(workDir, { recursive: true, force: true });
    fs.mkdirSync(workDir, { recursive: true });
    fs.copyFileSync(
      path.join(
        repoRoot,
        "engines",
        "thales",
        "tests",
        "fixtures",
        "tracer.ts",
      ),
      path.join(workDir, "tracer.ts"),
    );
    fs.writeFileSync(path.join(workDir, "parity.ts"), paritySource, "utf8");
    process.chdir(workDir);
  });
  afterAll(() => {
    process.chdir(repoRoot);
    fs.rmSync(workDir, { recursive: true, force: true });
  });

  it(
    "one healthy run: Theorem and Inappropriate per annotation",
    { timeout: 600_000 },
    () => {
      const prove = runMain(["prove", "tracer.ts"]);
      expect(prove.code, prove.stderr.join("\n")).toBe(0);
      expect(prove.stdout).toHaveLength(1);
      const env = JSON.parse(prove.stdout[0]!) as Envelope;
      expectValidEnvelope(env);

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
    { timeout: 600_000 },
    () => {
      const prove = runMain(["prove", "parity.ts"]);
      expect(prove.code, prove.stderr.join("\n")).toBe(0);
      const proveEnv = JSON.parse(prove.stdout[0]!) as Envelope;
      expectValidEnvelope(proveEnv);
      expect(proveEnv.annotations[0]).toMatchObject({ szs: "Theorem" });

      const refute = runMain(["refute", "parity.ts"]);
      expect(refute.code, refute.stderr.join("\n")).toBe(0);
      const refuteEnv = JSON.parse(refute.stdout[0]!) as Envelope;
      expectValidEnvelope(refuteEnv);

      const ids = (e: Envelope) =>
        e.annotations.map((a) => [a.file, a.function, a.property]).sort();
      expect(ids(proveEnv)).toEqual([["parity.ts", "add", "commutes"]]);
      expect(ids(proveEnv)).toEqual(ids(refuteEnv));
    },
  );
});
