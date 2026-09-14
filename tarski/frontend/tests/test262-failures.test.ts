// `tarski/test262/failures.md` against `tarski/test262/expected.json`.
//
// The table is written by hand — classifying a failure means reading the
// test, which no script can do — so this is what keeps it honest as the
// counts ratchet. A directory whose `fail` count moves has a row whose
// `fails` column no longer sums to it, and the suite says so before the
// expectations file is committed.

import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import type { Expectations } from "../src/test262/report.js";

const read = (name: string): string =>
  readFileSync(
    fileURLToPath(new URL(`../../test262/${name}`, import.meta.url)),
    "utf8",
  );

const expectations = JSON.parse(read("expected.json")) as Expectations;

/** One row of the failure list's table. */
interface Row {
  directory: string;
  fails: number;
  class: string;
  why: string;
  owner: string;
}

const CLASSES = ["builtin", "protocol", "out-of-scope", "bug"];

/**
 * The rows of the one markdown table in `failures.md`: the lines after the
 * header separator that start with a pipe, split on pipes and trimmed.
 */
function rows(markdown: string): Row[] {
  const lines = markdown.split("\n");
  const separator = lines.findIndex((line) => /^\|\s*-+\s*\|/.test(line));
  expect(separator).toBeGreaterThan(0);
  const out: Row[] = [];
  for (const line of lines.slice(separator + 1)) {
    if (!line.startsWith("|")) break;
    const cells = line
      .split("|")
      .slice(1, -1)
      .map((cell) => cell.trim());
    expect(cells).toHaveLength(5);
    out.push({
      directory: (cells[0] ?? "").replace(/`/g, ""),
      fails: Number(cells[1]),
      class: cells[2] ?? "",
      why: cells[3] ?? "",
      owner: cells[4] ?? "",
    });
  }
  return out;
}

describe("the failure list", () => {
  const table = rows(read("failures.md"));

  it("has rows", () => {
    expect(table.length).toBeGreaterThan(0);
  });

  it("names only directories the expectations file pins", () => {
    for (const row of table) {
      expect(Object.keys(expectations.directories)).toContain(row.directory);
    }
  });

  it("accounts for every failing directory", () => {
    const classified = new Set(table.map((row) => row.directory));
    for (const [directory, counts] of Object.entries(
      expectations.directories,
    )) {
      if (counts.fail > 0) expect(classified).toContain(directory);
    }
  });

  it("sums to each directory's pinned fail count", () => {
    const sums = new Map<string, number>();
    for (const row of table) {
      sums.set(row.directory, (sums.get(row.directory) ?? 0) + row.fails);
    }
    for (const [directory, sum] of sums) {
      expect({ directory, sum }).toEqual({
        directory,
        sum: expectations.directories[directory]?.fail,
      });
    }
  });

  it("classifies every row as one of the four kinds", () => {
    for (const row of table) {
      expect(CLASSES).toContain(row.class);
    }
  });

  it("gives every row an issue to wait on and a reason", () => {
    for (const row of table) {
      expect(row.owner).toMatch(/^#\d+$/);
      expect(row.why.length).toBeGreaterThan(0);
    }
  });

  it("counts a positive number of failures per row", () => {
    for (const row of table) {
      expect(Number.isInteger(row.fails)).toBe(true);
      expect(row.fails).toBeGreaterThan(0);
    }
  });
});
