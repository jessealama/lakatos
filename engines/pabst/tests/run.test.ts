import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { childConfig, runTests, vitestEntry } from "../src/run.js";
import { encodeIssue } from "../src/contract.js";
import { FALSIFIED } from "./helpers/fixtures.js";

const repoRoot = process.cwd();

// The fixture specs import vitest, resolved by walking up node_modules from
// cwd, so these projects live inside the repo tree (gitignored under
// .lakatos/), not os.tmpdir(). The child runs under lakatos's own config,
// so nothing here needs one. Fixture tests are *.spec.ts so the OUTER
// suite's include (tests/**/*.test.ts) never collects a leftover copy from
// a crashed run.
const workDir = path.join(repoRoot, ".lakatos", "runtest");

// Where these tests tell runTests to write its results, relative to whichever
// fixture directory the run happens in.
const RESULTS = path.join("out", "vitest-results.json");
const okDir = path.join(workDir, "ok");
const crashDir = path.join(workDir, "crash");
const brokenDir = path.join(workDir, "broken");

const SAMPLE_SPEC = `import { it, expect } from "vitest";
it("passes", () => { expect(1).toBe(1); });
it("fails", () => {
  throw new Error(${JSON.stringify(encodeIssue(FALSIFIED))});
});
`;

function inDir<T>(dir: string, fn: () => T): T {
  const prev = process.cwd();
  process.chdir(dir);
  try {
    return fn();
  } finally {
    process.chdir(prev);
  }
}

describe("runTests", () => {
  beforeAll(() => {
    fs.rmSync(workDir, { recursive: true, force: true });
    fs.mkdirSync(okDir, { recursive: true });
    fs.mkdirSync(crashDir, { recursive: true });
    fs.writeFileSync(path.join(okDir, "sample.spec.ts"), SAMPLE_SPEC, "utf8");
    // A spec that throws at import time: vitest survives to write results,
    // but with success:false and zero counted test failures.
    fs.mkdirSync(brokenDir, { recursive: true });
    fs.writeFileSync(
      path.join(brokenDir, "sample.spec.ts"),
      `throw new Error("boom: import exploded");\n`,
      "utf8",
    );
  });
  afterAll(() => {
    fs.rmSync(workDir, { recursive: true, force: true });
  });

  it(
    "returns the parsed vitest JSON from a completed run",
    { timeout: 60000 },
    () => {
      const result = inDir(okDir, () => runTests(".", RESULTS));
      expect(result.kind).toBe("completed");
      if (result.kind !== "completed") return;
      expect(result.json.numPassedTests).toBe(1);
      expect(result.json.numFailedTests).toBe(1);
      expect(result.json.success).toBe(false);
    },
  );

  it("writes results to a caller-provided path", { timeout: 60000 }, () => {
    const result = inDir(okDir, () => runTests(".", "custom-results.json"));
    expect(result.kind).toBe("completed");
    expect(fs.existsSync(path.join(okDir, "custom-results.json"))).toBe(true);
  });

  it("reports no-results when the stale results file cannot be cleared", () => {
    const result = inDir(okDir, () => {
      fs.rmSync(RESULTS, { force: true });
      fs.mkdirSync(RESULTS, { recursive: true });
      try {
        return runTests(".", RESULTS);
      } finally {
        fs.rmSync(RESULTS, { recursive: true, force: true });
      }
    });
    expect(result.kind).toBe("no-results");
    if (result.kind !== "no-results") return;
    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain(RESULTS);
  });

  it("launches lakatos's own vitest under this node, not npx", () => {
    const launches: [string, string[]][] = [];
    const capture = (cmd: string, args: string[]) => {
      launches.push([cmd, args]);
      return { status: 1, signal: null, stdout: "", stderr: "" };
    };
    inDir(okDir, () => runTests(".", RESULTS, capture));
    expect(launches).toHaveLength(1);
    const [cmd, args] = launches[0]!;
    expect(cmd).toBe(process.execPath);
    expect(args[0]).toBe(vitestEntry());
    expect(fs.existsSync(vitestEntry())).toBe(true);
    expect(args.slice(1, 3)).toEqual(["run", "."]);
  });

  it("launches the child with lakatos's own config, never the cwd's", () => {
    const launches: [string, string[]][] = [];
    const capture = (cmd: string, args: string[]) => {
      launches.push([cmd, args]);
      return { status: 1, signal: null, stdout: "", stderr: "" };
    };
    inDir(okDir, () => runTests(".", RESULTS, capture));
    const args = launches[0]![1];
    const at = args.indexOf("--config");
    expect(at).toBeGreaterThan(0);
    expect(args[at + 1]).toBe(childConfig());
    expect(path.isAbsolute(childConfig())).toBe(true);
    expect(fs.existsSync(childConfig())).toBe(true);
  });

  it("surfaces the spawn error when vitest cannot be launched", () => {
    // spawnSync's shape for a launch failure: no status, no streams.
    const unlaunchable = () => ({
      status: null,
      signal: null,
      stdout: null,
      stderr: null,
      error: Object.assign(new Error("spawnSync node ENOENT"), {
        code: "ENOENT",
      }),
    });
    const result = inDir(okDir, () => runTests(".", RESULTS, unlaunchable));
    expect(result.kind).toBe("no-results");
    if (result.kind !== "no-results") return;
    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain("ENOENT");
  });

  it(
    "reports a broken run when a test file fails to load",
    { timeout: 60000 },
    () => {
      const result = inDir(brokenDir, () => runTests(".", RESULTS));
      expect(result.kind).toBe("broken-run");
      if (result.kind !== "broken-run") return;
      expect(result.status).not.toBe(0);
      expect(result.messages.join("\n")).toContain("boom: import exploded");
    },
  );

  it("reports the signal when vitest was killed at the user's request", () => {
    // Results the dying vitest managed to write are not this run's story:
    // the interruption outranks whatever landed on disk.
    const killed = () => {
      fs.mkdirSync(path.dirname(RESULTS), { recursive: true });
      fs.writeFileSync(
        RESULTS,
        JSON.stringify({
          numPassedTests: 9,
          numFailedTests: 0,
          success: true,
          testResults: [],
        }),
        "utf8",
      );
      return {
        status: null,
        signal: "SIGINT" as const,
        stdout: null,
        stderr: null,
      };
    };
    const result = inDir(okDir, () => runTests(".", RESULTS, killed));
    expect(result).toEqual({ kind: "interrupted", signal: "SIGINT" });
  });

  it("keeps the engine's own failures out of the interrupted path", () => {
    // A vitest killed by a timeout carries ETIMEDOUT beside its SIGTERM.
    const timedOut = () => ({
      status: null,
      signal: "SIGTERM" as const,
      stdout: "",
      stderr: "",
      error: Object.assign(new Error("spawnSync node ETIMEDOUT"), {
        code: "ETIMEDOUT",
      }),
    });
    const result = inDir(okDir, () => runTests(".", RESULTS, timedOut));
    expect(result.kind).toBe("no-results");
  });

  it(
    "reports no-results when vitest dies before writing results, ignoring a stale results file",
    { timeout: 60000 },
    () => {
      const prev = process.env.NODE_OPTIONS;
      // A flag node refuses in NODE_OPTIONS kills the child before vitest
      // runs, so no reporter ever writes the results file.
      process.env.NODE_OPTIONS = "--bogus-flag";
      let result;
      try {
        result = inDir(crashDir, () => {
          fs.mkdirSync(path.dirname(RESULTS), { recursive: true });
          fs.writeFileSync(
            RESULTS,
            JSON.stringify({
              numPassedTests: 9,
              numFailedTests: 0,
              success: true,
              testResults: [],
            }),
            "utf8",
          );
          return runTests(".", RESULTS);
        });
      } finally {
        if (prev === undefined) delete process.env.NODE_OPTIONS;
        else process.env.NODE_OPTIONS = prev;
      }
      expect(result.kind).toBe("no-results");
      if (result.kind !== "no-results") return;
      expect(result.status).not.toBe(0);
      expect(result.stdout + result.stderr).toContain(
        "not allowed in NODE_OPTIONS",
      );
    },
  );
});
