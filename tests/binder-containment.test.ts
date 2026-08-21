import fc from "fast-check";
import { describe, expect, it } from "vitest";
import { numberDoubleConstraints } from "../lemma/src/domains.js";
import { parseRange } from "../lemma/src/range.js";
import { numberGuard } from "../engines/thales/frontend/src/transcribe.js";

/**
 * The invariant: the prover's binder domain must CONTAIN the refuter's.
 *
 * The two engines read an interval differently and cannot be made to agree.
 * lemma fixes its denotation in fast-check's total order over doubles, where
 * every double is distinct, -0 sits below 0, and an excluded endpoint removes
 * exactly one double by adjacency. The prover gets the same interval as Lean
 * hypotheses, where the comparisons are IEEE: they cannot separate -0 from 0
 * and have no notion of adjacency.
 *
 * Containment in this direction is what makes the divergence safe — a prover
 * Theorem can then never contradict a refuter counterexample, and the worst
 * case is failing to prove something the refuter could not falsify anyway.
 *
 * Checking it needs no Lean: JavaScript's < and <= on `number` are the same
 * IEEE-754 binary64 comparisons as Lean's on `Float`, down to how they treat
 * the zeros. What the op strings MEAN on the Lean side is the one leg this
 * cannot see, and `Test/ThalesDsl/BoundRelationTest.lean` pins that.
 */

/** Interval spellings, each named for the drift it encodes. */
const CORPUS: { text: string; hazard: string }[] = [
  {
    text: "[-1, 0)",
    hazard: "refuter yields -0; a strict upper bound at 0 would drop it",
  },
  {
    text: "(-0, 0]",
    hazard: "denotes exactly {0}; a strict lower bound at -0 empties it",
  },
  {
    text: "[-0, 0]",
    hazard: "both zeros as closed endpoints",
  },
  {
    text: "(0, 1]",
    hazard: "an excluded 0 the prover must genuinely exclude",
  },
  {
    text: "[-1, -0)",
    hazard: "excluded -0 as the upper endpoint",
  },
  {
    text: "[0, ∞)",
    hazard: "prover carries no upper bound; refuter excludes +∞",
  },
  {
    text: "(-∞, 0]",
    hazard: "prover carries no lower bound; refuter excludes -∞",
  },
  {
    text: "(-∞, ∞)",
    hazard: "prover quantifies over every Float, bounds absent on both sides",
  },
  { text: "(0, 1)", hazard: "an ordinary open interval" },
  { text: "[-1.5, 2.5]", hazard: "an ordinary closed interval" },
  {
    text: "(5e-324, 1e-323]",
    hazard: "adjacent subnormals — one double wide once the bound is excluded",
  },
];

/** Whether a value satisfies the guard the transcriber emits for `range`.
 * The comparisons are JS's, which are Lean's `Float` comparisons. */
function satisfiesGuard(v: number, guard: ReturnType<typeof numberGuard>) {
  // An absent bound is no hypothesis at all on the prover's side, so it
  // constrains nothing — which is exactly how an infinite endpoint drifts.
  const lo =
    !guard.lo || (guard.lo.op === "<=" ? guard.lo.val <= v : guard.lo.val < v);
  const hi =
    !guard.hi || (guard.hi.op === "<=" ? v <= guard.hi.val : v < guard.hi.val);
  return lo && hi;
}

describe("the prover's number binder domain contains the refuter's", () => {
  for (const { text, hazard } of CORPUS) {
    it(`${text} — ${hazard}`, () => {
      const range = parseRange(text, "number");
      const guard = numberGuard(range);
      // A fixed seed keeps a failure reproducible; the sample is wide enough
      // to reach the endpoints, which is where every known drift lives.
      const values = fc.sample(fc.double(numberDoubleConstraints(range)), {
        numRuns: 2000,
        seed: 42,
      });
      const escaped = values.filter((v) => !satisfiesGuard(v, guard));
      expect(escaped.map((v) => (Object.is(v, -0) ? "-0" : String(v)))).toEqual(
        [],
      );
    });
  }

  it("samples the endpoints themselves, so the corpus can catch endpoint drift", () => {
    // The check above is only as good as what fast-check hands it: if the
    // sample never reached an interval's endpoints, a wrong bound there
    // would pass unnoticed.
    const range = parseRange("[-1, 0)", "number");
    const values = fc.sample(fc.double(numberDoubleConstraints(range)), {
      numRuns: 2000,
      seed: 42,
    });
    expect(values.some((v) => Object.is(v, -0))).toBe(true);
  });
});
