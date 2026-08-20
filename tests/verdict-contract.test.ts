import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { PROVE_STATUSES } from "../src/szs.js";

const verdictLean = readFileSync(
  fileURLToPath(
    new URL("../engines/thales/ThalesDsl/Verdict.lean", import.meta.url),
  ),
  "utf8",
);

describe("verdict-channel contract", () => {
  it("the emitting side enumerates exactly the CLI's statuses", () => {
    const decl = verdictLean.match(
      /inductive Szs where\n([\s\S]*?)\n\s*deriving/,
    );
    expect(decl, "the Szs declaration was not found").not.toBeNull();
    const constructors = [...decl![1]!.matchAll(/\|\s*(\w+)/g)].map(
      (m) => m[1],
    );
    expect(new Set(constructors)).toEqual(new Set(PROVE_STATUSES));
  });

  it("every status goes on the wire under its own name", () => {
    const body = verdictLean.match(/def Szs\.toString[\s\S]*?\n\n/);
    expect(body, "Szs.toString was not found").not.toBeNull();
    const arms = [...body![0].matchAll(/\|\s*\.(\w+)\s*=>\s*"([^"]+)"/g)].map(
      (m) => [m[1], m[2]] as const,
    );
    expect(new Set(arms.map(([name]) => name))).toEqual(
      new Set(PROVE_STATUSES),
    );
    for (const [name, wire] of arms) expect(wire).toBe(name);
  });
});
