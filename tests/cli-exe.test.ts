import { describe, expect, it, vi } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { runMainRaw, useTempProject } from "./helpers/cli.js";
import { RUN_ROOT } from "../src/run-dir.js";
import type { BinaryResult } from "../tarski/frontend/src/binary.js";

// The evaluator is mocked at the module seam the prove tests use for
// thales, and only its *build* is: `runDocument` stays real, so the spawn
// path, the argv, and the exit-code classification are all exercised
// against `fake-tarski.mjs` — a stand-in that obeys a marker literal in
// the document it is handed. The real binary is exercised under
// LAKATOS_TARSKI_E2E in `exe-e2e.test.ts`.
const FAKE = fileURLToPath(
  new URL("../tarski/frontend/tests/fixtures/fake-tarski.mjs", import.meta.url),
);

vi.mock("../tarski/frontend/src/binary.js", async () => {
  const actual = await vi.importActual<
    typeof import("../tarski/frontend/src/binary.js")
  >("../tarski/frontend/src/binary.js");
  return {
    ...actual,
    ensureBinary: vi.fn((): BinaryResult => ({ kind: "ready", binary: FAKE })),
  };
});
const { ensureBinary } = await import("../tarski/frontend/src/binary.js");
const ensureBinaryMock = vi.mocked(ensureBinary);

/** A marked program. The marker survives type stripping because it is a
 * string literal in a declaration, which is exactly how the test262 fake
 * tree carries its own. */
const marked = (instruction: string, extra = ""): string =>
  `const marker: string = "fake: ${instruction}";\n${extra}`;

describe("lakatos exe", () => {
  useTempProject("lakatos-cli-exe-", {
    "clean.ts": marked("exit 0"),
    "throws.ts": marked("exit 1 Uncaught RangeError: zero"),
    "template.ts": marked("exit 3 unsupported: TemplateExpression"),
    "malformed.ts": marked("exit 2 tarski: x: malformed"),
    "other.ts": marked("exit 0"),
  });

  it("refuses a run with no file", async () => {
    const r = await runMainRaw(["exe"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("usage: lakatos exe");
  });

  it("refuses a run with two files", async () => {
    const r = await runMainRaw(["exe", "clean.ts", "other.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("usage: lakatos exe");
  });

  it("refuses a glob that names more than one file", async () => {
    const r = await runMainRaw(["exe", "*.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("usage: lakatos exe");
  });

  it("runs a clean program and writes both artifacts", async () => {
    const r = await runMainRaw(["exe", "clean.ts"]);
    expect(r.code).toBe(0);
    expect(r.stdout).toBe("");
    // exe announces no run directory — its stderr is the program's — so
    // the artifacts are found the way a user would find them.
    const runs = fs
      .readdirSync(RUN_ROOT, { withFileTypes: true })
      .filter((e) => e.isDirectory())
      .map((e) => e.name)
      .sort();
    const dir = path.join(RUN_ROOT, runs.at(-1)!, "tarski");
    const script = fs.readFileSync(path.join(dir, "clean.js"), "utf8");
    expect(script.startsWith('"use strict";')).toBe(true);
    expect(script).not.toContain("export");
    expect(fs.existsSync(path.join(dir, "clean.json"))).toBe(true);
  });

  it("forwards an uncaught throw's report and exits 1", async () => {
    const r = await runMainRaw(["exe", "throws.ts"]);
    expect(r.code).toBe(1);
    expect(r.stderr).toContain("Uncaught RangeError: zero");
  });

  it("names the node kind the evaluator does not know and exits 2", async () => {
    const r = await runMainRaw(["exe", "template.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain(
      "lakatos: template.ts: unsupported syntax: TemplateExpression",
    );
  });

  it("forwards a refusal of the document and exits 2", async () => {
    const r = await runMainRaw(["exe", "malformed.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("tarski: x: malformed");
    expect(r.stderr).toContain(
      "lakatos: the evaluator refused the document lakatos handed it",
    );
  });

  it("reports a missing evaluator and exits 2", async () => {
    ensureBinaryMock.mockReturnValueOnce({
      kind: "no-project",
      message: "the tarski evaluator is not part of this installation",
    });
    const r = await runMainRaw(["exe", "clean.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain(
      "lakatos: the tarski evaluator is not part of this installation",
    );
  });

  it("reports a failed build with both streams and exits 2", async () => {
    ensureBinaryMock.mockReturnValueOnce({
      kind: "failed",
      stdout: "building Tarski.Realm\n",
      stderr: "error: Realm.lean:1:0: boom\n",
    });
    const r = await runMainRaw(["exe", "clean.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("building Tarski.Realm");
    expect(r.stderr).toContain("error: Realm.lean:1:0: boom");
    expect(r.stderr).toContain("lakatos: lake build tarski failed");
  });
});

describe("lakatos exe's typecheck gate", () => {
  useTempProject(
    "lakatos-cli-exe-no-tsconfig-",
    { "clean.ts": marked("exit 0") },
    { tsconfig: false },
  );

  it("refuses a project with no tsconfig.json", async () => {
    const r = await runMainRaw(["exe", "clean.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("lakatos: no tsconfig.json:");
  });
});

describe("lakatos exe on a program that does not type check", () => {
  useTempProject("lakatos-cli-exe-illtyped-", {
    "bad.ts": "const n: number = 'x';\n",
  });

  it("reports each diagnostic and refuses the run", async () => {
    const r = await runMainRaw(["exe", "bad.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("TS2322");
    expect(r.stderr).toContain(
      "lakatos: the program does not type check under lakatos's required options",
    );
  });
});

describe("lakatos exe on a file the program leaves out", () => {
  useTempProject(
    "lakatos-cli-exe-outside-",
    {
      "tsconfig.json": JSON.stringify({
        compilerOptions: { target: "es2022", module: "nodenext", types: [] },
        include: ["src"],
        exclude: [".lakatos"],
      }),
      "src/inside.ts": marked("exit 0"),
      "outside.ts": marked("exit 0"),
    },
    { tsconfig: false },
  );

  it("refuses it in the issue's own words", async () => {
    const r = await runMainRaw(["exe", "outside.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain(
      "lakatos: outside.ts is not part of the program tsconfig.json describes, so it was not type checked",
    );
  });
});
