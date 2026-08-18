import { describe, it, expect } from "vitest";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import type { Envelope } from "../src/envelope.js";

const META = {
  version: "0.1.0",
  startedAt: "2026-08-17T00:00:00.000Z",
  cwd: "/tmp/proj",
};

describe("envelope schema", () => {
  it("accepts a refute envelope with all four annotation shapes", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        seed: 42,
        generated: 4,
        passed: 1,
        failed: 3,
        annotations: [
          {
            file: "f.ts",
            function: "clamp",
            property: "hi",
            szs: "CounterSatisfiable",
            kind: "falsified",
            counterexample: { x: -1 },
          },
          {
            file: "f.ts",
            function: "Counter#inc",
            property: "th",
            szs: "Error",
            kind: "threw",
            counterexample: { x: 0 },
            error: "boom",
          },
          {
            file: "f.ts",
            function: "f",
            property: "ex",
            szs: "GaveUp",
            kind: "exhausted",
            error: "too many skipped runs",
          },
          { file: "f.ts", function: "g", property: "ok", szs: "GaveUp" },
        ],
      }),
    ).not.toThrow();
  });

  it("accepts a stub envelope without run stats", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          { file: "f.ts", function: "f", property: "p", szs: "NotTried" },
        ],
      }),
    ).not.toThrow();
  });

  it("rejects a falsified annotation whose szs is not CounterSatisfiable", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "GaveUp",
            kind: "falsified",
            counterexample: { x: 1 },
          },
        ],
      }),
    ).toThrow();
  });

  it("accepts a Theorem annotation (property proven)", () => {
    const envelope: Envelope = {
      ...META,
      annotations: [
        { file: "f.ts", function: "f", property: "p", szs: "Theorem" },
      ],
    };
    expect(() => expectValidEnvelope(envelope)).not.toThrow();
  });

  it("accepts an Inappropriate annotation carrying its reason", () => {
    const envelope: Envelope = {
      ...META,
      annotations: [
        {
          file: "f.ts",
          function: "f",
          property: "p",
          szs: "Inappropriate",
          reason: "calls fetch(), which is outside the mappable subset",
        },
      ],
    };
    expect(() => expectValidEnvelope(envelope)).not.toThrow();
  });

  it("rejects an Inappropriate annotation without a reason", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          { file: "f.ts", function: "f", property: "p", szs: "Inappropriate" },
        ],
      }),
    ).toThrow();
  });

  it("rejects an unknown szs value", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          { file: "f.ts", function: "f", property: "p", szs: "Satisfiable" },
        ],
      }),
    ).toThrow();
  });
});
