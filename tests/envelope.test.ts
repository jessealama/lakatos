import { describe, it, expect } from "vitest";
import { encodeIssue } from "../engines/pabst/src/contract.js";
import type {
  AssertionResult,
  VitestJson,
} from "../engines/pabst/src/vitest-json.js";
import {
  buildEnvelope,
  notTriedEnvelope,
  type PropertyIdentity,
} from "../src/envelope.js";

const META = {
  version: "0.1.0",
  startedAt: "2026-08-17T00:00:00.000Z",
  cwd: "/tmp/proj",
  seed: 42,
  generated: 3,
};

const IDS: PropertyIdentity[] = [
  { file: "foo.ts", function: "clamp", property: "upper bound" },
  { file: "foo.ts", function: "clamp", property: "lower bound" },
  { file: "foo.ts", function: "abs", property: "non-negative" },
];

function failed(message: string): AssertionResult {
  return { status: "failed", failureMessages: [message] };
}
const passed: AssertionResult = { status: "passed", failureMessages: [] };

function json(
  results: AssertionResult[],
  passedN: number,
  failedN: number,
): VitestJson {
  return {
    numPassedTests: passedN,
    numFailedTests: failedN,
    success: failedN === 0,
    testResults: [{ assertionResults: results }],
  };
}

describe("buildEnvelope", () => {
  it("joins issues onto identities and marks the rest GaveUp", () => {
    const v = json(
      [
        failed(
          encodeIssue({
            file: "foo.ts",
            function: "clamp",
            property: "upper bound",
            kind: "falsified",
            counterexample: { x: -1 },
          }),
        ),
        passed,
        passed,
      ],
      2,
      1,
    );
    const env = buildEnvelope(META, v, IDS);
    expect(env.version).toBe("0.1.0");
    expect(env.seed).toBe(42);
    expect(env.passed).toBe(2);
    expect(env.failed).toBe(1);
    expect(env.annotations).toEqual([
      {
        file: "foo.ts",
        function: "clamp",
        property: "upper bound",
        szs: "CounterSatisfiable",
        kind: "falsified",
        counterexample: { x: -1 },
      },
      {
        file: "foo.ts",
        function: "clamp",
        property: "lower bound",
        szs: "GaveUp",
      },
      {
        file: "foo.ts",
        function: "abs",
        property: "non-negative",
        szs: "GaveUp",
      },
    ]);
  });

  it("maps threw to Error and carries the error text", () => {
    const v = json(
      [
        failed(
          encodeIssue({
            file: "foo.ts",
            function: "abs",
            property: "non-negative",
            kind: "threw",
            counterexample: { x: 0 },
            error: "boom",
          }),
        ),
        passed,
        passed,
      ],
      2,
      1,
    );
    const env = buildEnvelope(META, v, IDS);
    expect(env.annotations[2]).toEqual({
      file: "foo.ts",
      function: "abs",
      property: "non-negative",
      szs: "Error",
      kind: "threw",
      counterexample: { x: 0 },
      error: "boom",
    });
  });

  it("maps exhausted to GaveUp but keeps the kind", () => {
    const v = json(
      [
        failed(
          encodeIssue({
            file: "foo.ts",
            function: "clamp",
            property: "lower bound",
            kind: "exhausted",
            error: "too many skipped runs",
          }),
        ),
        passed,
        passed,
      ],
      2,
      1,
    );
    const env = buildEnvelope(META, v, IDS);
    expect(env.annotations[1]).toEqual({
      file: "foo.ts",
      function: "clamp",
      property: "lower bound",
      szs: "GaveUp",
      kind: "exhausted",
      error: "too many skipped runs",
    });
  });
});

describe("notTriedEnvelope", () => {
  it("marks every identity NotTried and omits run stats", () => {
    const env = notTriedEnvelope("0.1.0", META.startedAt, META.cwd, IDS);
    expect(env.seed).toBeUndefined();
    expect(env.generated).toBeUndefined();
    expect(env.passed).toBeUndefined();
    expect(env.failed).toBeUndefined();
    expect(env.annotations).toHaveLength(3);
    expect(env.annotations.every((a) => a.szs === "NotTried")).toBe(true);
  });
});
