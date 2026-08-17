import { describe, it, expect, beforeAll } from "vitest";
import { execFileSync, spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";

const root = process.cwd();
const cliJs = path.join(root, "dist", "src", "cli.js");

// npm exposes the package's bin as a symlink (node_modules/.bin/lakatos ->
// dist/src/cli.js), so these tests run the *built* CLI the way an installed
// copy runs: executed by node with argv[1] naming the symlink, not the real
// file. Neither property is visible to the in-process suites that import
// main().
describe("dist/src/cli.js as an installed bin", () => {
  beforeAll(() => {
    execFileSync("npx", ["tsc", "-p", "tsconfig.json"], { cwd: root });
  }, 60_000);

  it("starts with an env-node shebang", () => {
    const firstLine = fs.readFileSync(cliJs, "utf8").split("\n", 1)[0];
    expect(firstLine).toBe("#!/usr/bin/env node");
  });

  it("runs main() when invoked through a .bin-style symlink", () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "lakatos-bin-"));
    const link = path.join(dir, "lakatos");
    fs.symlinkSync(cliJs, link);
    try {
      const r = spawnSync(process.execPath, [link], { encoding: "utf8" });
      expect(r.stderr).toContain("usage: lakatos");
      expect(r.status).toBe(2);
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  });
});
