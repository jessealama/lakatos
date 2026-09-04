import { describe, it, expect } from "vitest";
import { encodeIssue, type Issue } from "../engines/pabst/src/contract.js";
import type { ProveStatus } from "../src/szs.js";
import type {
  AssertionResult,
  VitestJson,
} from "../engines/pabst/src/vitest-json.js";
import {
  buildEnvelope,
  collectIssues,
  identityOf,
  interruptedResults,
  joinProveVerdicts,
  joinRefuteVerdicts,
  type AnnotationResult,
  type PlannedProperty,
  type PropertyIdentity,
  type ProveVerdict,
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

describe("collectIssues", () => {
  const FALSIFIED: Issue = {
    file: "a.ts",
    function: "f",
    property: "p",
    kind: "falsified",
    counterexample: { x: 1 },
  };
  const THREW: Issue = {
    file: "a.ts",
    function: "f",
    property: "q",
    kind: "threw",
    counterexample: { x: 0 },
    error: "boom",
  };
  const EXHAUSTED: Issue = {
    file: "a.ts",
    function: "f",
    property: "r",
    kind: "exhausted",
    error: "too many skipped runs",
  };
  // Realistic failure message: the sentinel arrives wrapped in an Error
  // rendering with a stack trace, not bare.
  function wrapped(issue: Issue): AssertionResult {
    return failed(`Error: ${encodeIssue(issue)}\n    at x`);
  }

  it("collects only failed assertions and parses each issue", () => {
    const v = json(
      [passed, wrapped(FALSIFIED), wrapped(THREW), wrapped(EXHAUSTED)],
      1,
      3,
    );
    expect(collectIssues(v)).toEqual({
      issues: [FALSIFIED, THREW, EXHAUSTED],
      unreadable: [],
    });
  });

  it("tolerates missing testResults and assertionResults arrays", () => {
    expect(collectIssues({} as VitestJson)).toEqual({
      issues: [],
      unreadable: [],
    });
    expect(
      collectIssues({ testResults: [{}] } as unknown as VitestJson),
    ).toEqual({ issues: [], unreadable: [] });
  });

  it("tolerates a failed assertion with no failureMessages array", () => {
    expect(
      collectIssues(
        json([{ status: "failed" } as unknown as AssertionResult], 0, 1),
      ),
    ).toEqual({
      issues: [],
      unreadable: ["a failed test carries no failure message"],
    });
  });

  it("finds a payload sitting behind an unrelated failure message", () => {
    const a: AssertionResult = {
      status: "failed",
      failureMessages: [
        "Error: some unrelated failure\n  at foo (x.ts:1:1)",
        encodeIssue(FALSIFIED),
      ],
    };
    expect(collectIssues(json([a], 0, 1)).issues).toEqual([FALSIFIED]);
  });

  it("reports a failed assertion with no readable payload as unreadable", () => {
    const a: AssertionResult = {
      status: "failed",
      failureMessages: ["Error: boom\n  at foo (x.ts:1:1)"],
    };
    expect(collectIssues(json([a], 0, 1))).toEqual({
      issues: [],
      unreadable: [
        "a failed test carries no readable issue payload: Error: boom",
      ],
    });
  });

  it("reports a failed assertion with no failure message at all", () => {
    expect(
      collectIssues(json([{ status: "failed", failureMessages: [] }], 0, 1)),
    ).toEqual({
      issues: [],
      unreadable: ["a failed test carries no failure message"],
    });
    expect(collectIssues(json([failed("")], 0, 1))).toEqual({
      issues: [],
      unreadable: ["a failed test carries no failure message"],
    });
  });
});

describe("joinRefuteVerdicts", () => {
  const ISSUE: Issue = {
    file: "foo.ts",
    function: "clamp",
    property: "upper bound",
    kind: "falsified",
    counterexample: { n: 0 },
  };

  it("joins parsed issues onto identities", () => {
    const v = json([failed(encodeIssue(ISSUE))], 2, 1);
    expect(joinRefuteVerdicts(IDS, v)).toEqual({
      kind: "joined",
      annotations: [
        {
          ...IDS[0],
          szs: "CounterSatisfiable",
          kind: "falsified",
          counterexample: { n: 0 },
        },
        { ...IDS[1], szs: "GaveUp" },
        { ...IDS[2], szs: "GaveUp" },
      ],
    });
  });

  it("an unreadable failure withholds every verdict", () => {
    const v = json(
      [failed(encodeIssue(ISSUE)), failed("Error: boom\n  at x")],
      1,
      2,
    );
    expect(joinRefuteVerdicts(IDS, v)).toEqual({
      kind: "unreadable",
      messages: [
        "a failed test carries no readable issue payload: Error: boom",
      ],
    });
  });

  it("a planned enumeration with no issue is a Theorem with its case count", () => {
    const planned: PlannedProperty[] = [{ ...IDS[0]!, cases: 10 }, IDS[1]!];
    const v = json([passed, passed], 2, 0);
    expect(joinRefuteVerdicts(planned, v)).toEqual({
      kind: "joined",
      annotations: [
        { ...IDS[0], szs: "Theorem", kind: "enumerated", cases: 10 },
        { ...IDS[1], szs: "GaveUp" },
      ],
    });
  });

  it("an enumeration that found a counterexample carries no case count", () => {
    const planned: PlannedProperty[] = [{ ...IDS[0]!, cases: 10 }];
    const v = json([failed(encodeIssue(ISSUE))], 0, 1);
    expect(joinRefuteVerdicts(planned, v)).toEqual({
      kind: "joined",
      annotations: [
        {
          ...IDS[0],
          szs: "CounterSatisfiable",
          kind: "falsified",
          counterexample: { n: 0 },
        },
      ],
    });
  });

  it("a budget issue is a Timeout carrying the reason", () => {
    const planned: PlannedProperty[] = [{ ...IDS[0]!, cases: 1000 }];
    const v = json(
      [
        failed(
          encodeIssue({
            ...IDS[0]!,
            kind: "budget",
            reason:
              "evaluated 412 of 1000 cases within the time budget, no counterexample",
          }),
        ),
      ],
      0,
      1,
    );
    expect(joinRefuteVerdicts(planned, v)).toEqual({
      kind: "joined",
      annotations: [
        {
          ...IDS[0],
          szs: "Timeout",
          kind: "budget",
          reason:
            "evaluated 412 of 1000 cases within the time budget, no counterexample",
        },
      ],
    });
  });
});

describe("identityOf", () => {
  it("drops planning detail so no envelope entry inherits it", () => {
    expect(identityOf({ ...IDS[0]!, cases: 10 } as PlannedProperty)).toEqual(
      IDS[0],
    );
  });

  it("interrupted results never carry a case count", () => {
    expect(interruptedResults([{ ...IDS[0]!, cases: 10 }], "SIGINT")).toEqual([
      { ...IDS[0], szs: "User", reason: "the run was interrupted (SIGINT)" },
    ]);
  });
});

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

  it("a refutation is reported even when its payload is not the first message", () => {
    const issue: Issue = {
      file: "foo.ts",
      function: "clamp",
      property: "upper bound",
      kind: "falsified",
      counterexample: { n: 0 },
    };
    const a: AssertionResult = {
      status: "failed",
      failureMessages: [
        "Error: some unrelated failure\n  at foo (x.ts:1:1)",
        encodeIssue(issue),
      ],
    };
    const env = buildEnvelope(META, json([a], 2, 1), IDS);
    expect(env.annotations[0]).toEqual({
      ...IDS[0],
      szs: "CounterSatisfiable",
      kind: "falsified",
      counterexample: { n: 0 },
    });
  });

  it("throws on an unreadable failure instead of shipping GaveUp", () => {
    const v = json([failed("Error: boom\n  at x")], 0, 1);
    expect(() => buildEnvelope(META, v, IDS)).toThrow(
      /no readable issue payload/,
    );
  });
});

describe("joinProveVerdicts", () => {
  const id = (fn: string): PropertyIdentity => ({
    file: "t.ts",
    function: fn,
    property: "p",
  });
  const verdict = (
    fn: string,
    szs: ProveStatus,
    reason = "r",
  ): ProveVerdict => ({
    identity: ["t.ts", fn, "p"],
    szs,
    reason,
  });

  it("maps each status to its envelope shape", () => {
    const join = joinProveVerdicts(
      [id("a"), id("b"), id("c"), id("d"), id("e")],
      [
        verdict(
          "a",
          "Theorem",
          "proved by a decision procedure over the bounded domain, kernel-checked as X",
        ),
        verdict("b", "Inappropriate", "await is unmapped"),
        verdict("c", "Error", "elaboration failed"),
        verdict("d", "GaveUp", "decide failed"),
        verdict("e", "NotTried", "no structured property"),
      ],
    );
    expect(join).toEqual({
      kind: "joined",
      annotations: [
        { ...id("a"), szs: "Theorem", axioms: [] },
        { ...id("b"), szs: "Inappropriate", reason: "await is unmapped" },
        { ...id("c"), szs: "Error", error: "elaboration failed" },
        { ...id("d"), szs: "GaveUp", reason: "decide failed" },
        { ...id("e"), szs: "NotTried", reason: "no structured property" },
      ],
    });
  });

  it("order follows the identities, not the verdict lines", () => {
    const join = joinProveVerdicts(
      [id("a"), id("b")],
      [verdict("b", "Theorem"), verdict("a", "Theorem")],
    );
    expect(join.kind).toBe("joined");
    expect(
      (join as { annotations: AnnotationResult[] }).annotations.map(
        (a) => a.function,
      ),
    ).toEqual(["a", "b"]);
  });

  it("a missing verdict is a mismatch naming the annotation", () => {
    const join = joinProveVerdicts(
      [id("a"), id("b")],
      [verdict("a", "Theorem")],
    );
    expect(join.kind).toBe("mismatched");
    expect((join as { messages: string[] }).messages.join("\n")).toContain(
      '"b"',
    );
  });

  it("a surplus verdict is a mismatch", () => {
    expect(
      joinProveVerdicts(
        [id("a")],
        [verdict("a", "Theorem"), verdict("ghost", "Theorem")],
      ).kind,
    ).toBe("mismatched");
  });

  it("a duplicate verdict is a mismatch", () => {
    expect(
      joinProveVerdicts(
        [id("a")],
        [verdict("a", "Theorem"), verdict("a", "GaveUp")],
      ).kind,
    ).toBe("mismatched");
  });

  it("a Theorem verdict ships the axioms its proof rests on", () => {
    const join = joinProveVerdicts(
      [id("a")],
      [{ ...verdict("a", "Theorem"), axioms: ["Lean.ofReduceBool"] }],
    );
    expect(join).toEqual({
      kind: "joined",
      annotations: [
        { ...id("a"), szs: "Theorem", axioms: ["Lean.ofReduceBool"] },
      ],
    });
  });

  it("a CounterSatisfiable verdict ships kind falsified and the counterexample", () => {
    const join = joinProveVerdicts(
      [id("a")],
      [
        {
          ...verdict("a", "CounterSatisfiable", "false on its bounded domain"),
          counterexample: { x: 0, y: "9007199254740992" },
        },
      ],
    );
    expect(join).toEqual({
      kind: "joined",
      annotations: [
        {
          ...id("a"),
          szs: "CounterSatisfiable",
          kind: "falsified",
          counterexample: { x: 0, y: "9007199254740992" },
        },
      ],
    });
  });

  it("a CounterSatisfiable verdict without a counterexample is a mismatch", () => {
    const join = joinProveVerdicts(
      [id("a")],
      [verdict("a", "CounterSatisfiable")],
    );
    expect(join.kind).toBe("mismatched");
    expect((join as { messages: string[] }).messages.join("\n")).toContain(
      "counterexample",
    );
  });

  it("a CounterSatisfiable verdict with an empty counterexample is a mismatch", () => {
    // The envelope schema requires a non-empty counterexample object, so
    // an empty one must not ship on a healthy run.
    const join = joinProveVerdicts(
      [id("a")],
      [{ ...verdict("a", "CounterSatisfiable"), counterexample: {} }],
    );
    expect(join.kind).toBe("mismatched");
    expect((join as { messages: string[] }).messages.join("\n")).toContain(
      "counterexample",
    );
  });

  it("a status the envelope cannot represent is a mismatch", () => {
    // Only a broken engine sends this, so the type has to be forced.
    const bogus = verdict("a", "Unknown" as ProveStatus);
    expect(joinProveVerdicts([id("a")], [bogus]).kind).toBe("mismatched");
  });

  it("a Timeout verdict joins with its reason", () => {
    const join = joinProveVerdicts([id("a")], [verdict("a", "Timeout")]);
    expect(join.kind).toBe("joined");
  });
});
