import { describe, expect, it } from "vitest";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import * as path from "node:path";
import { executeSource, type ExeDeps } from "../src/exe.js";
import type { SpawnOutcome } from "../tarski/frontend/src/binary.js";
import { schemaValidator } from "./helpers/schema-validator.js";

const validate = schemaValidator(
  new URL("../schemas/tarski-estree.schema.json", import.meta.url),
  "the ESTree document exe handed the evaluator",
);

/** Deps whose build is ready and whose run answers what the test says. */
function deps(run: Partial<SpawnOutcome>): ExeDeps {
  return {
    ensureBinary: () => ({ kind: "ready", binary: "/bin/tarski" }),
    runDocument: () => ({ status: 0, stdout: "", stderr: "", ...run }),
  };
}

describe("executeSource", () => {
  const dir = mkdtempSync(path.join(tmpdir(), "lakatos-exe-"));

  const run = (source: string, d: ExeDeps, name = "t.ts") =>
    executeSource(source, name, path.join(dir, name), d);

  it("passes a clean run's streams through", () => {
    expect(run("console.log(1);", deps({ status: 0, stdout: "1\n" }))).toEqual({
      kind: "ran",
      status: 0,
      stdout: "1\n",
      stderr: "",
    });
  });

  it("passes an uncaught throw through with its exit status", () => {
    expect(
      run(
        "throw new RangeError('zero');",
        deps({ status: 1, stderr: "Uncaught RangeError: zero\n" }),
      ),
    ).toEqual({
      kind: "ran",
      status: 1,
      stdout: "",
      stderr: "Uncaught RangeError: zero\n",
    });
  });

  it("names the node kind the evaluator refused", () => {
    expect(
      run(
        "const s = `x`;",
        deps({ status: 3, stderr: "unsupported: TemplateExpression\n" }),
      ),
    ).toEqual({ kind: "unsupported", node: "TemplateExpression" });
  });

  it("falls back to the whole line when the marker is absent", () => {
    expect(
      run("const x = 1;", deps({ status: 3, stderr: "something else\n" })),
    ).toEqual({ kind: "unsupported", node: "something else" });
  });

  it("reports a refusal of the document with the binary's own stderr", () => {
    expect(
      run(
        "const x = 1;",
        deps({ status: 2, stderr: "tarski: t.json: malformed\n" }),
      ),
    ).toEqual({ kind: "refused", stderr: "tarski: t.json: malformed\n" });
  });

  it("reports a spawn error as a refusal, with its text", () => {
    const r = run(
      "const x = 1;",
      deps({ status: null, signal: "SIGKILL", error: new Error("boom") }),
    );
    expect(r).toEqual({ kind: "refused", stderr: "Error: boom\n" });
  });

  // A spawn that never started — a binary that is not where it was said to
  // be — answers with both streams null, not empty.
  it("survives a spawn that produced no streams at all", () => {
    expect(
      run(
        "const x = 1;",
        deps({
          status: null,
          stdout: null,
          stderr: null,
          error: new Error("spawnSync /bin/tarski ENOENT"),
        }),
      ),
    ).toEqual({
      kind: "refused",
      stderr: "Error: spawnSync /bin/tarski ENOENT\n",
    });
  });

  it("passes a missing project through", () => {
    expect(
      run("const x = 1;", {
        ensureBinary: () => ({
          kind: "no-project",
          message: "no evaluator here",
        }),
        runDocument: () => expect.fail("the binary should not have been run"),
      }),
    ).toEqual({ kind: "no-project", message: "no evaluator here" });
  });

  it("passes a failed build through with both streams", () => {
    expect(
      run("const x = 1;", {
        ensureBinary: () => ({ kind: "failed", stdout: "out", stderr: "err" }),
        runDocument: () => expect.fail("the binary should not have been run"),
      }),
    ).toEqual({ kind: "build-failed", stdout: "out", stderr: "err" });
  });

  // The two artifacts are what a user reads when the evaluator refuses
  // something, so they are written before the binary is ever spawned.
  it("writes the stripped script and a schema-valid document", () => {
    const out = path.join(dir, "artifacts");
    executeSource(
      "export const k: number = 2;\nconsole.log(k);\n",
      "k.ts",
      out,
      deps({ status: 0 }),
    );
    expect(readFileSync(path.join(out, "k.js"), "utf8")).toBe(
      '"use strict";\nconst k = 2;\nconsole.log(k);\n',
    );
    validate(JSON.parse(readFileSync(path.join(out, "k.json"), "utf8")));
  });

  it("cleans up", () => {
    rmSync(dir, { recursive: true, force: true });
  });
});
