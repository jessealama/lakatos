import { describe, expect, it } from "vitest";
import { runMainRaw, useTempProject } from "./helpers/cli.js";
import { BUILD_TIMEOUT_MS } from "../tarski/frontend/src/binary.js";

// `lakatos exe` against the *real* evaluator, which needs a lakatos
// checkout with the Lean toolchain — `tarski.yml` is the one workflow with
// both Node and Lean in a single job. Everywhere else this suite skips,
// and `cli-exe.test.ts` covers the same contract against the fake binary.
const e2e = process.env.LAKATOS_TARSKI_E2E === "1";

// The first case pays for one `lake build tarski`; a warm cache makes it a
// no-op, a cold one does not.
const FIRST_TIMEOUT_MS = BUILD_TIMEOUT_MS + 60_000;

describe.runIf(e2e)("lakatos exe end to end", () => {
  useTempProject("lakatos-exe-e2e-", {
    // #386's example, verbatim.
    "foo.ts":
      'export function inv(x: number): number { if (x === 0) throw new RangeError("zero"); return 1 / x; }\n' +
      "console.log(inv(4));\n" +
      "console.log(inv(0));\n",
    "clean.ts": 'console.log("a", 1);\n',
    "last.ts": "const k: number = 2;\nk + 1;\n",
    "template.ts": "const s: string = `x${1}`;\nconsole.log(s);\n",
  });

  it(
    "prints what ran and reports the uncaught throw, exiting 1",
    { timeout: FIRST_TIMEOUT_MS },
    async () => {
      const r = await runMainRaw(["exe", "foo.ts"]);
      expect(r.stdout).toBe("0.25\n");
      expect(r.stderr).toBe("Uncaught RangeError: zero\n");
      expect(r.code).toBe(1);
    },
  );

  it("forwards every argument of a console.log call", async () => {
    const r = await runMainRaw(["exe", "clean.ts"]);
    expect(r.stdout).toBe("a 1\n");
    expect(r.stderr).toBe("");
    expect(r.code).toBe(0);
  });

  // `exec`'s one difference from `run`: a program is executed for its
  // effects, so its completion value is not a line of output — as `node
  // file.js` prints none.
  it("prints no completion value", async () => {
    const r = await runMainRaw(["exe", "last.ts"]);
    expect(r.stdout).toBe("");
    expect(r.code).toBe(0);
  });

  it("names the syntax the evaluator does not know and exits 2", async () => {
    const r = await runMainRaw(["exe", "template.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain("unsupported syntax: TemplateExpression");
  });
});

describe.runIf(e2e)("lakatos exe on a file outside the program", () => {
  useTempProject(
    "lakatos-exe-e2e-outside-",
    {
      "tsconfig.json": JSON.stringify({
        compilerOptions: { target: "es2022", module: "nodenext", types: [] },
        include: ["src"],
        exclude: [".lakatos"],
      }),
      "src/inside.ts": "const k: number = 1;\n",
      "not-in-tsconfig.ts": 'console.log("never");\n',
    },
    { tsconfig: false },
  );

  it("refuses it before the evaluator is ever built", async () => {
    const r = await runMainRaw(["exe", "not-in-tsconfig.ts"]);
    expect(r.code).toBe(2);
    expect(r.stderr).toContain(
      "lakatos: not-in-tsconfig.ts is not part of the program tsconfig.json describes, so it was not type checked",
    );
  });
});
