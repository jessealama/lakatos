import { describe, it, expect } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import {
  runForEnvelope,
  runMain,
  useRepoScratchDir,
  useTempProject,
} from "./helpers/cli.js";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";

const SCALE =
  "export function scale(x: number, factor: number): number {\n" +
  "  return x * factor;\n" +
  "}\n";

const REPROS = {
  "j.ts":
    SCALE +
    "/** @ensures{p} forall (x: int ∈ [0, 5)) { scale(x) >= 0 } */\n" +
    "export function id(x: number): number {\n  return x;\n}\n",
  "q.ts":
    "/** @ensures{p} forall (x: int ∈ [0, 5)) { f(x) + q >= 0 } */\n" +
    "export function f(x: number): number {\n  return x;\n}\n",
  "b.ts":
    "/** @ensures{p} forall (x: int ∈ [0, 5)) { h(x) } */\n" +
    "export function h(x: number): number {\n  return x;\n}\n",
  "hidden.ts":
    "function g(x: number): number { return x; }\n" +
    "/** @ensures{p} forall (x: int ∈ [0, 5)) { g(x) > 0 } */\n" +
    "export function f(x: number): number { return x; }\n",
  "sibling.ts":
    "/** @ensures{bad} forall (x: int ∈ [0, 5)) { f(x) } */\n" +
    "/** @ensures{good} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */\n" +
    "export function f(x: number): number { return x; }\n",
};

const EXPECTED = {
  "j.ts": {
    function: "id",
    error:
      "j.ts:4: @ensures{p}: in atom `scale(x) >= 0`: TS2554: Expected 2 arguments, but got 1.",
  },
  "q.ts": {
    function: "f",
    error:
      "q.ts:1: @ensures{p}: in atom `f(x) + q >= 0`: TS2304: Cannot find name 'q'.",
  },
  "b.ts": {
    function: "h",
    error:
      "b.ts:1: @ensures{p}: in atom `h(x)`: TS1360: Type 'number' does not satisfy the expected type 'boolean'.",
  },
  "hidden.ts": {
    function: "f",
    error:
      "hidden.ts:2: @ensures{p}: in atom `g(x) > 0`: 'g' is not exported from hidden.ts; " +
      "a formula may name only the module's exports and the host's standard globals",
  },
} as const;

describe.each(["prove", "refute", "check"] as const)(
  "%s: a type fault inside an atom is the annotation's InputError",
  (command) => {
    useTempProject(`lakatos-island-${command}-`, REPROS);

    it.each(Object.keys(EXPECTED) as Array<keyof typeof EXPECTED>)(
      "%s reports InputError naming the atom and exits 2",
      async (file) => {
        const { code, stdout, stderr } = await runMain([command, file]);
        expect(code).toBe(2);
        expect(stdout).toHaveLength(1);
        const env = JSON.parse(stdout[0]!);
        expectValidEnvelope(env);
        expect(env.annotations).toEqual([
          {
            file,
            function: EXPECTED[file].function,
            property: "p",
            szs: "InputError",
            error: EXPECTED[file].error,
          },
        ]);
        expect(stderr).toContain(`error: ${EXPECTED[file].error}`);
        // No engine saw the annotation: the spine counts nothing to run.
        expect(stderr.join("\n")).toMatch(
          /emitted 0 annotations|generated 0 properties|not implemented/,
        );
      },
    );
  },
);

describe("check: a sound sibling of a faulty annotation still reports", () => {
  useTempProject("lakatos-island-sibling-check-", REPROS);

  it("lists InputError beside NotTried", async () => {
    const { code, stdout } = await runMain(["check", "sibling.ts"]);
    expect(code).toBe(2);
    const env = JSON.parse(stdout[0]!);
    expectValidEnvelope(env);
    expect(env.annotations).toEqual([
      { file: "sibling.ts", function: "f", property: "good", szs: "NotTried" },
      {
        file: "sibling.ts",
        function: "f",
        property: "bad",
        szs: "InputError",
        error:
          "sibling.ts:1: @ensures{bad}: in atom `f(x)`: TS1360: Type 'number' does not satisfy the expected type 'boolean'.",
      },
    ]);
  });
});

describe("refute: a sound sibling of a faulty annotation still runs", () => {
  const repoRoot = process.cwd();
  useRepoScratchDir(
    path.join(repoRoot, ".lakatos", "island-sibling"),
    (dir) => {
      fs.writeFileSync(
        path.join(dir, "sibling.ts"),
        REPROS["sibling.ts"],
        "utf8",
      );
    },
  );

  it(
    "gets its verdict beside the InputError, exit 2",
    { timeout: 60000 },
    async () => {
      const env = await runForEnvelope(["refute", "sibling.ts"], 2);
      expect(env).toMatchObject({ generated: 1, passed: 1, failed: 0 });
      expect(env.annotations).toEqual([
        {
          file: "sibling.ts",
          function: "f",
          property: "good",
          szs: "Theorem",
          kind: "enumerated",
          cases: 5,
        },
        {
          file: "sibling.ts",
          function: "f",
          property: "bad",
          szs: "InputError",
          error:
            "sibling.ts:1: @ensures{bad}: in atom `f(x)`: TS1360: Type 'number' does not satisfy the expected type 'boolean'.",
        },
      ]);
    },
  );
});
