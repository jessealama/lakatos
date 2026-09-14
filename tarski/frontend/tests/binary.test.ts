import { describe, expect, it } from "vitest";
import * as path from "node:path";
import {
  BUILD_TIMEOUT_MS,
  ensureBinary,
  runDocument,
  type Spawn,
  type SpawnOutcome,
} from "../src/binary.js";
import { defaultBinary } from "../src/test262/paths.js";

/** A spawn that records its call and answers what the test dictates. */
function recording(outcome: Partial<SpawnOutcome>): {
  spawn: Spawn;
  calls: { cmd: string; args: string[]; opts: Record<string, unknown> }[];
} {
  const calls: {
    cmd: string;
    args: string[];
    opts: Record<string, unknown>;
  }[] = [];
  const spawn: Spawn = (cmd, args, opts) => {
    calls.push({ cmd, args, opts });
    return { status: 0, stdout: "", stderr: "", ...outcome };
  };
  return { spawn, calls };
}

const enoent = (): Error => {
  const e = new Error("spawnSync lake ENOENT") as NodeJS.ErrnoException;
  e.code = "ENOENT";
  return e;
};

describe("ensureBinary", () => {
  it("reports no project when there is no tarski package to build", () => {
    const { spawn, calls } = recording({});
    const r = ensureBinary(undefined, spawn);
    expect(r).toEqual({
      kind: "no-project",
      message:
        "the tarski evaluator is not part of this installation; run exe from a lakatos checkout",
    });
    // Nothing was spawned: there was nowhere to spawn it.
    expect(calls).toHaveLength(0);
  });

  it("reports no project when lake is not on PATH", () => {
    const { spawn } = recording({ error: enoent(), status: null });
    const r = ensureBinary("/somewhere/tarski", spawn);
    expect(r.kind).toBe("no-project");
    expect(r.kind === "no-project" && r.message).toContain(
      "lake was not found on PATH",
    );
  });

  it("carries both streams out of a failed build", () => {
    const { spawn } = recording({
      status: 1,
      stdout: "building\n",
      stderr: "error: Realm.lean:1:0\n",
    });
    expect(ensureBinary("/somewhere/tarski", spawn)).toEqual({
      kind: "failed",
      stdout: "building\n",
      stderr: "error: Realm.lean:1:0\n",
    });
  });

  it("carries a spawn error's text out beside stderr", () => {
    const { spawn } = recording({
      status: null,
      error: new Error("boom"),
      stderr: "partial\n",
    });
    const r = ensureBinary("/somewhere/tarski", spawn);
    expect(r.kind).toBe("failed");
    expect(r.kind === "failed" && r.stderr).toBe("partial\nError: boom\n");
  });

  it("builds the binary target in the package and answers where it landed", () => {
    const { spawn, calls } = recording({ status: 0 });
    expect(ensureBinary("/somewhere/tarski", spawn)).toEqual({
      kind: "ready",
      binary: defaultBinary("/somewhere/tarski"),
    });
    expect(calls).toEqual([
      {
        cmd: "lake",
        args: ["build", "tarski"],
        opts: {
          cwd: "/somewhere/tarski",
          encoding: "utf8",
          timeout: BUILD_TIMEOUT_MS,
        },
      },
    ]);
  });

  it("puts the binary where the test262 runner looks for it", () => {
    expect(defaultBinary("/r")).toBe(
      path.join("/r", ".lake", "build", "bin", "tarski"),
    );
  });
});

describe("runDocument", () => {
  // No timeout: a program that diverges hangs as it would under `node`,
  // and the Ctrl-C that ends the user's wait ends both processes.
  it("runs the document under exec with no timeout", () => {
    const { spawn, calls } = recording({ status: 0, stdout: "0.25\n" });
    const r = runDocument("/bin/tarski", "/tmp/t.json", spawn);
    expect(r.stdout).toBe("0.25\n");
    expect(calls).toEqual([
      {
        cmd: "/bin/tarski",
        args: ["exec", "/tmp/t.json"],
        opts: { encoding: "utf8", maxBuffer: 256 * 1024 * 1024 },
      },
    ]);
  });
});
