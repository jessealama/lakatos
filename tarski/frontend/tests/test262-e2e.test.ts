import { describe, it, expect, beforeAll } from "vitest";
import { existsSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import path from "node:path";

// What ties the fake binary to the real one. Every other test in this
// suite runs `fixtures/fake-tarski.mjs`, whose exit codes and stderr
// shapes are a transcription of `Tarski/Main.lean`'s contract; this run
// puts the actual binary in its place over the same tree and demands the
// same table. Lean is not installed in `lakatos.yml`, so this runs under
// `LAKATOS_TARSKI_E2E=1` in `tarski.yml`, where it is.
const root = fileURLToPath(new URL("../../..", import.meta.url));
const TREE = fileURLToPath(new URL("fixtures/test262", import.meta.url));
const CLI = path.join(
  root,
  "dist",
  "tarski",
  "frontend",
  "src",
  "test262",
  "cli.js",
);
const BINARY = path.join(root, "tarski", ".lake", "build", "bin", "tarski");
const FAKE = fileURLToPath(
  new URL("fixtures/fake-tarski.mjs", import.meta.url),
);

const run = (binary: string): { status: number | null; stdout: string } => {
  const result = spawnSync(
    process.execPath,
    [CLI, "test", "--test262", TREE, "--binary", binary, "--timeout", "2000"],
    { encoding: "utf8" },
  );
  return { status: result.status, stdout: result.stdout };
};

describe.runIf(process.env.LAKATOS_TARSKI_E2E === "1")(
  "the built binary over the fake tree",
  () => {
    // Two runs of the whole tree, read by the four cases below. Each one
    // pays `test/timeout/loops.js` at the full `--timeout 2000` plus a
    // node spawn per test, so each is paid once and none of the cases
    // leans on vitest's five-second default.
    let real: { status: number | null; stdout: string };
    let fake: { status: number | null; stdout: string };
    beforeAll(() => {
      real = run(BINARY);
      fake = run(FAKE);
    }, 60_000);

    it("is where lake build tarski puts it", () => {
      expect(existsSync(BINARY)).toBe(true);
    }, 10_000);

    it("produces exactly the table the fake binary does", () => {
      expect(real.status).toBe(0);
      expect(real.stdout).toBe(fake.stdout);
    }, 10_000);

    it("passes the tests the fake tree says pass", () => {
      expect(real.stdout).toContain(
        "test/pass              6     0            0        0              0        0",
      );
    }, 10_000);

    it("refuses a $262 hook as unsupported rather than failing it", () => {
      expect(real.stdout).toContain("$262.evalScript  1");
    }, 10_000);
  },
);
