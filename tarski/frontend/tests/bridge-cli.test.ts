import { describe, it, expect, vi } from "vitest";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { main } from "../src/bridge-cli.js";

const root = process.cwd();

const fixture = (name: string): string =>
  fileURLToPath(new URL(`fixtures/${name}`, import.meta.url));

const golden = (name: string): string => readFileSync(fixture(name), "utf8");

/** Run `main` with stdout and stderr captured, as the command's caller
 * sees them. */
function invoke(...argv: string[]): {
  status: number;
  stdout: string;
  stderr: string;
} {
  let stdout = "";
  let stderr = "";
  const out = vi
    .spyOn(process.stdout, "write")
    .mockImplementation((chunk: unknown) => {
      stdout += String(chunk);
      return true;
    });
  const err = vi.spyOn(console, "error").mockImplementation((...args) => {
    stderr += `${args.join(" ")}\n`;
  });
  try {
    return { status: main(argv), stdout, stderr };
  } finally {
    out.mockRestore();
    err.mockRestore();
  }
}

describe("the bridge as a command", () => {
  it("writes the golden document to stdout", () => {
    const r = invoke(fixture("numeric-loop.js"));
    expect(r.status).toBe(0);
    expect(r.stdout).toBe(golden("numeric-loop.estree.json"));
  });

  it("writes to a file when given an output path", () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tarski-bridge-"));
    try {
      const out = path.join(dir, "out.json");
      const r = invoke(fixture("arithmetic.js"), out);
      expect(r.status).toBe(0);
      expect(r.stdout).toBe("");
      expect(readFileSync(out, "utf8")).toBe(golden("arithmetic.estree.json"));
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it("reports usage with no arguments", () => {
    const r = invoke();
    expect(r.status).toBe(2);
    expect(r.stderr).toContain("usage: tarski-bridge");
  });

  it("reports usage with too many arguments", () => {
    const r = invoke("a.js", "b.json", "c");
    expect(r.status).toBe(2);
    expect(r.stderr).toContain("usage: tarski-bridge");
  });

  it("reports an unreadable input", () => {
    const r = invoke(path.join(root, "no-such-file.js"));
    expect(r.status).toBe(2);
    expect(r.stderr).toContain("tarski-bridge:");
  });

  it("reports a syntax error rather than emitting a document", () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tarski-bridge-"));
    try {
      const bad = path.join(dir, "bad.js");
      writeFileSync(bad, '"use strict";\nlet = ;\n');
      const r = invoke(bad);
      expect(r.status).toBe(2);
      expect(r.stdout).toBe("");
      expect(r.stderr).toContain("bad.js:2:");
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  // The Lean side is run on its own copies of these documents in CI, and
  // the two must not drift: the schema is only a seam if both languages
  // see the same bytes.
  for (const name of [
    "numeric-loop",
    "counter",
    "errors",
    "uncaught",
    "harness-floor",
    "compare-array",
  ]) {
    it(`agrees with the copy the Lean tests are run against for ${name}`, () => {
      const lean = path.join(
        root,
        "tarski",
        "Test",
        "Tarski",
        "fixtures",
        `${name}.json`,
      );
      expect(readFileSync(lean, "utf8")).toBe(golden(`${name}.estree.json`));
    });
  }
});

// The built file, run the way a person runs it: `node dist/.../
// bridge-cli.js t.js > t.json`. The build is the suite-wide globalSetup's.
describe("dist/tarski/frontend/src/bridge-cli.js", () => {
  const cli = path.join(
    root,
    "dist",
    "tarski",
    "frontend",
    "src",
    "bridge-cli.js",
  );

  it("starts with an env-node shebang", () => {
    expect(readFileSync(cli, "utf8").split("\n", 1)[0]).toBe(
      "#!/usr/bin/env node",
    );
  });

  it("runs main() when node executes it", () => {
    const r = spawnSync(process.execPath, [cli, fixture("numeric-loop.js")], {
      encoding: "utf8",
    });
    expect(r.status).toBe(0);
    expect(r.stdout).toBe(golden("numeric-loop.estree.json"));
  });
});
