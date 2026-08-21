import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { expectValidEnvelope } from "./helpers/envelope-schema.js";
import type { Envelope } from "../src/envelope.js";
import { SZS_STATUSES } from "../src/szs.js";
import { QUALIFIED_NAME_PATTERN } from "../lemma/src/index.js";

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

  it("accepts a prove refutation in the same falsified shape refute uses", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "CounterSatisfiable",
            kind: "falsified",
            counterexample: { x: 0, y: "9007199254740992" },
          },
        ],
      }),
    ).not.toThrow();
  });

  it("rejects a CounterSatisfiable annotation without a counterexample", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "CounterSatisfiable",
            kind: "falsified",
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

  it("accepts an InputError annotation carrying its diagnostic", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "Point#norm",
            property: "nonneg",
            szs: "InputError",
            error:
              "@ensures on method 'norm' of class 'Point', which is not exported from f.ts",
          },
          {
            file: "f.ts",
            function: "<anonymous>#m",
            property: "p",
            szs: "InputError",
            error:
              "@ensures on method 'm' of an anonymous class in f.ts (anonymous classes are not supported)",
          },
        ],
      }),
    ).not.toThrow();
  });

  it("rejects an InputError annotation without a diagnostic", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          { file: "f.ts", function: "f", property: "p", szs: "InputError" },
        ],
      } as unknown as Envelope),
    ).toThrow();
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

  it("accepts prove-pipeline reasons on kindless GaveUp and NotTried", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "GaveUp",
            reason: "decide failed: the goal is not decidable",
          },
          {
            file: "f.ts",
            function: "g",
            property: "q",
            szs: "NotTried",
            reason: "no structured property provided",
          },
        ],
      }),
    ).not.toThrow();
  });

  it("accepts a Timeout with its budget reason", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "Timeout",
            reason:
              "the attempt exceeded the per-annotation heartbeat budget (thales.heartbeats = 1)",
          },
        ],
      }),
    ).not.toThrow();
  });

  it("accepts a NotTried with the unsupported-range kind and reason", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "NotTried",
            kind: "unsupported-range",
            reason:
              "endpoint 1000000000000000000000000000000 exceeds the safe integer range (±9007199254740991)",
          },
        ],
      }),
    ).not.toThrow();
  });

  it("rejects an unsupported-range entry without a reason", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "NotTried",
            kind: "unsupported-range",
          },
        ],
      } as unknown as Envelope),
    ).toThrow();
  });

  it("rejects the unsupported-range kind on a GaveUp entry", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "GaveUp",
            kind: "unsupported-range",
            reason: "r",
          },
        ],
      } as unknown as Envelope),
    ).toThrow();
  });

  it("accepts a prover Error carrying only its diagnostic", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "Error",
            error: "property elaboration failed",
          },
        ],
      }),
    ).not.toThrow();
  });

  it("rejects an Error annotation with no diagnostic at all", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          { file: "f.ts", function: "f", property: "p", szs: "Error" },
        ],
      }),
    ).toThrow();
  });

  it("rejects an empty prove reason", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "GaveUp",
            reason: "",
          },
        ],
      }),
    ).toThrow();
  });

  it("rejects a reason on a Theorem entry", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "Theorem",
            reason:
              "proved by a decision procedure over the bounded domain, kernel-checked as TsProof.thm_1",
          },
        ],
      }),
    ).toThrow();
  });

  it("rejects a reason on an exhausted (kinded) GaveUp", () => {
    expect(() =>
      expectValidEnvelope({
        ...META,
        annotations: [
          {
            file: "f.ts",
            function: "f",
            property: "p",
            szs: "GaveUp",
            kind: "exhausted",
            error: "too many skipped runs",
            reason: "does not belong here",
          },
        ],
      } as unknown as Envelope),
    ).toThrow();
  });

  it("gives every status a shape, and no shape a status off the list", () => {
    const schema = readFileSync(
      fileURLToPath(
        new URL("../schemas/envelope.schema.json", import.meta.url),
      ),
      "utf8",
    );
    const named = new Set<string>();
    const collect = (node: unknown): void => {
      if (Array.isArray(node)) return node.forEach(collect);
      if (typeof node !== "object" || node === null) return;
      const o = node as Record<string, unknown>;
      const szs = (o.properties as Record<string, unknown> | undefined)?.szs as
        { const?: string; enum?: string[] } | undefined;
      if (szs?.const !== undefined) named.add(szs.const);
      for (const v of szs?.enum ?? []) named.add(v);
      Object.values(o).forEach(collect);
    };
    collect(JSON.parse(schema));
    expect(named).toEqual(new Set(SZS_STATUSES));
  });

  it("keeps the schema's functionName pattern in sync with the builder's", () => {
    const schema = JSON.parse(
      readFileSync(
        fileURLToPath(
          new URL("../schemas/envelope.schema.json", import.meta.url),
        ),
        "utf8",
      ),
    );
    expect(schema.definitions.functionName.pattern).toBe(
      QUALIFIED_NAME_PATTERN.source,
    );
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
