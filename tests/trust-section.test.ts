import { describe, it, expect } from "vitest";
import { existsSync, readFileSync } from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

const SPEC = path.join(REPO, "spec", "semantics.md");
const spec = readFileSync(SPEC, "utf8");
const readme = readFileSync(path.join(REPO, "README.md"), "utf8");

const HEADING = "### What a Theorem rests on";

/** GitHub's slug for a heading: lower-case, spaces to hyphens, drop the rest. */
function slug(heading: string): string {
  return heading
    .replace(/^#+\s*/, "")
    .toLowerCase()
    .replace(/[^\w\s-]/g, "")
    .trim()
    .replace(/\s+/g, "-");
}

/** From a heading to the next heading at the same level or above, or to EOF. */
function section(text: string, heading: string, stop: RegExp): string {
  const start = text.indexOf(heading);
  expect(start, `${heading} is missing`).toBeGreaterThanOrEqual(0);
  const rest = text.slice(start + heading.length);
  const end = stop.exec(rest);
  return heading + (end === null ? rest : rest.slice(0, end.index));
}

const trust = section(spec, HEADING, /^## /m);

describe("the trust section", () => {
  it("appears once, under the verdict section", () => {
    expect(spec.match(/^### What a Theorem rests on$/gm)).toHaveLength(1);
    const verdicts = spec.indexOf("## Verdicts and SZS statuses");
    const here = spec.indexOf(HEADING);
    expect(verdicts).toBeGreaterThanOrEqual(0);
    expect(here).toBeGreaterThan(verdicts);
    expect(
      spec.slice(verdicts + 1, here).match(/^## /m),
      "a later `##` section opened before the trust section: it is no longer " +
        "part of Verdicts and SZS statuses",
    ).toBeNull();
  });

  it("links the committed test262 results table", () => {
    const targets = [...trust.matchAll(/\]\(([^)]+)\)/g)].map(([, t]) => t!);
    const resolved = targets.map((t) => path.resolve(REPO, "spec", t));
    for (const [i, file] of resolved.entries()) {
      expect(existsSync(file), `${targets[i]} does not resolve to a file`).toBe(
        true,
      );
    }
    expect(
      resolved,
      "the section must link tarski/test262/results.md; if the table moved, " +
        "repoint this link (and tarski/CLAUDE.md's note about it)",
    ).toContain(path.join(REPO, "tarski", "test262", "results.md"));
  });

  it("states the two limits", () => {
    expect(trust).toMatch(/only the primitives are shared/i);
    expect(trust).toMatch(/runs on Node/);
    expect(trust).toMatch(/V8/);
  });

  it("names no tactic, Lean version, or internal module", () => {
    const forbidden = [
      "native_decide",
      "decide",
      "simp",
      "omega",
      "partial_fixpoint",
      "ThalesDsl",
      "#thales_prove",
      "Js/",
      "Tarski/",
      ".lean",
    ];
    expect(forbidden.filter((word) => trust.includes(word))).toEqual([]);
    expect(trust).not.toMatch(/\bv?4\.\d+\.\d+/);
  });

  it("is what the islands section points forward to", () => {
    expect(spec).not.toContain("trust reporting below");
    expect(
      section(spec, "### Islands (host expressions)", /^#{2,3} /m),
    ).toMatch(/What a Theorem rests on\* below/);
  });
});

describe("the README", () => {
  it("points at the trust section from its architecture section", () => {
    const architecture = section(readme, "## Architecture", /^## /m);
    expect(architecture).toContain(`spec/semantics.md#${slug(HEADING)}`);
  });
});
