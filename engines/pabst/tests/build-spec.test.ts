import { describe, it, expect } from "vitest";
import { buildSpecs } from "../src/build-spec.js";
import { LemmaError } from "../../../lemma/src/index.js";

const FIXTURE = new URL("./fixtures/e2e/readme-example.ts", import.meta.url)
  .pathname;

describe("buildSpecs", () => {
  it("produces a PropertySpec for the README's worked example", () => {
    const { specs } = buildSpecs(FIXTURE);
    expect(specs).toHaveLength(1);
    const s = specs[0]!;
    expect(s.name).toBe("nonzero");
    expect(s.functionName).toBe("foo");
    expect(s.binders).toEqual([
      { varName: "x", domain: "bigint" },
      { varName: "y", domain: "number" },
    ]);
    expect(s.preconditions).toEqual([
      '__bool(Number.isInteger(y), "Number.isInteger(y)")',
    ]);
    expect(s.body).toBe('__bool(foo(x, y) !== 0, "foo(x, y) !== 0")');
    expect(s.freeExports).toEqual(["foo"]);
    expect(s.location.line).toBeGreaterThan(0);
  });
});

const BAD_PREFIX = new URL(
  "./fixtures/build-spec/bad-prefix.ts",
  import.meta.url,
).pathname;

describe("buildSpecs — per-annotation diagnostics", () => {
  it("wraps a LemmaError with file:line/@ensures{name} and keeps the original as cause", () => {
    let err: unknown;
    try {
      buildSpecs(BAD_PREFIX);
    } catch (e) {
      err = e;
    }
    expect(err).toBeInstanceOf(LemmaError);
    const wrapped = err as LemmaError;
    expect(wrapped.message).toMatch(
      /bad-prefix\.ts:1: @ensures\{shapely\}: expected 'forall'/,
    );
    // The rewrap must not lose the original error: its stack points at the
    // actual throw site, not at the rewrap line.
    expect(wrapped.cause).toBeInstanceOf(LemmaError);
    expect((wrapped.cause as Error).message).toMatch(/^expected 'forall'/);
  });
});

const CLASS_OK = new URL("./fixtures/extract/class-ok.ts", import.meta.url)
  .pathname;

describe("buildSpecs — class methods", () => {
  it("carries className and isStatic onto the spec", () => {
    const { specs } = buildSpecs(CLASS_OK);
    const inc = specs.find((s) => s.functionName === "inc")!;
    expect(inc.className).toBe("Counter");
    expect(inc.isStatic).toBe(false);

    const of = specs.find((s) => s.functionName === "of")!;
    expect(of.className).toBe("Counter");
    expect(of.isStatic).toBe(true);

    const bump = specs.find((s) => s.functionName === "bump")!;
    expect(bump.className).toBeUndefined();
  });
});

const fixture = (name: string) =>
  new URL(`./fixtures/build-spec/${name}`, import.meta.url).pathname;

const HUGE = "1000000000000000000000000000000";

describe("buildSpecs — unrepresentable domains", () => {
  it("refuses a clamped annotation and keeps its neighbours testable", () => {
    const { specs, untried } = buildSpecs(fixture("clamped.ts"));
    expect(specs.map((s) => s.name)).toEqual(["ordinary"]);
    expect(untried.map((u) => u.name)).toEqual([
      "hugeCeiling",
      "hugeFloor",
      "hugeBoth",
    ]);
  });

  it("names the offending endpoints in the reason", () => {
    const { untried } = buildSpecs(fixture("clamped.ts"));
    const by = new Map(untried.map((u) => [u.name, u.reason]));
    expect(by.get("hugeCeiling")).toBe(
      `endpoint ${HUGE} exceeds the safe integer range (±9007199254740991)`,
    );
    expect(by.get("hugeFloor")).toBe(
      `endpoint -${HUGE} exceeds the safe integer range (±9007199254740991)`,
    );
    expect(by.get("hugeBoth")).toBe(
      `endpoints -${HUGE} and ${HUGE} exceed ` +
        `the safe integer range (±9007199254740991)`,
    );
  });

  it("carries the identity fields the envelope needs", () => {
    const { untried } = buildSpecs(fixture("clamped.ts"));
    const u = untried.find((u) => u.name === "hugeCeiling")!;
    expect(u.functionName).toBe("nonneg");
  });

  it("refuses an interval the clamp empties rather than aborting the run", () => {
    const { specs, untried } = buildSpecs(fixture("empty-after-clamp.ts"));
    expect(specs).toEqual([]);
    expect(untried).toHaveLength(1);
    expect(untried[0]!.name).toBe("emptied");
    expect(untried[0]!.reason).toBe(
      `endpoints ${HUGE} and ${HUGE}0 exceed ` +
        `the safe integer range (±9007199254740991)`,
    );
  });

  it("still rejects an interval empty as written: that is bad input", () => {
    expect(() => buildSpecs(fixture("empty-as-written.ts"))).toThrow(
      LemmaError,
    );
    expect(() => buildSpecs(fixture("empty-as-written.ts"))).toThrow(
      /empty interval: no int satisfies/,
    );
  });

  it("refuses a half-bounded interval whose written endpoint is beyond", () => {
    // The prover instead degrades this one to its bare command and proves
    // over all of Int; both engines stay on the safe side of the written
    // domain, so the divergence is deliberate.
    const { specs, untried } = buildSpecs(fixture("half-bounded-huge.ts"));
    expect(specs).toEqual([]);
    expect(untried.map((u) => u.name)).toEqual(["ceiling"]);
  });

  it("lets a second blocker keep its own diagnostic", () => {
    expect(() => buildSpecs(fixture("clamped-and-unresolvable.ts"))).toThrow(
      /nowhere/,
    );
  });
});
