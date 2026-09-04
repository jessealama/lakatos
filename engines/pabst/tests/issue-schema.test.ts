import { describe, it, expect } from "vitest";
import { expectValidIssue } from "./helpers/issue-schema.js";

describe("issue schema", () => {
  it("accepts a falsified issue with an instance-method name", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "Counter#inc",
        property: "p",
        kind: "falsified",
        counterexample: { x: 0 },
      }),
    ).not.toThrow();
  });

  it("accepts a falsified issue with a static-method name", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "Arith.negate",
        property: "p",
        kind: "falsified",
        counterexample: { x: 0 },
      }),
    ).not.toThrow();
  });

  it("accepts an exhausted issue", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "f",
        property: "p",
        kind: "exhausted",
        error: "too many skipped runs",
      }),
    ).not.toThrow();
  });

  it("accepts a budget issue with its reason", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "f",
        property: "p",
        kind: "budget",
        reason:
          "evaluated 412 of 1000 cases within the time budget, no counterexample",
      }),
    ).not.toThrow();
  });

  it("rejects a budget issue without a reason", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "f",
        property: "p",
        kind: "budget",
      }),
    ).toThrow();
  });

  it("rejects a budget issue carrying a counterexample it never found", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "f",
        property: "p",
        kind: "budget",
        reason:
          "evaluated 1 of 2 cases within the time budget, no counterexample",
        counterexample: { x: 1 },
      }),
    ).toThrow();
  });

  it("accepts $-containing identifiers, which are legal TypeScript", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "Cart#$total",
        property: "p",
        kind: "falsified",
        counterexample: { x: 0 },
      }),
    ).not.toThrow();
  });

  it("rejects a falsified issue with an empty counterexample", () => {
    // A falsified property must carry at least one binding — an empty
    // counterexample means the reporter lost the values it exists to report.
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "f",
        property: "p",
        kind: "falsified",
        counterexample: {},
      }),
    ).toThrow();
  });

  it("rejects a falsified issue that also carries an error", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "f",
        property: "p",
        kind: "falsified",
        counterexample: { x: 0 },
        error: "nope",
      }),
    ).toThrow();
  });

  it("rejects an unknown kind", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "f",
        property: "p",
        kind: "boom",
      }),
    ).toThrow();
  });

  it("rejects a malformed function name", () => {
    expect(() =>
      expectValidIssue({
        file: "f.ts",
        function: "1 bad",
        property: "p",
        kind: "falsified",
        counterexample: { x: 0 },
      }),
    ).toThrow();
  });
});
