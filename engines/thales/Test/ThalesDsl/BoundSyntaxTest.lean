import ThalesDsl.Prove

open Js ThalesDsl

ts_def "idf" := ts.fn(ts.param["a"](ts.number)) : ts.number {
  ts.return(ts.id["a"])
}

-- Both bounds, mixed strictness.
#thales_prove "b.ts" "idf" "both" :=
  ts.forall(ts.binder["a"](ts.number,
      ts.lower["<"](ts.fnum[0]), ts.upper["<="](ts.fnum[1]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  }

-- Lower bound only.
#thales_prove "b.ts" "idf" "lower" :=
  ts.forall(ts.binder["a"](ts.number, ts.lower["<="](ts.fnum[0]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  }

-- No bounds at all: the whole of binary64.
#thales_prove "b.ts" "idf" "none" :=
  ts.forall(ts.binder["a"](ts.number)) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  }

-- Infinite endpoints bound against the literal infinity: strict for an open
-- side, non-strict for a closed one.

-- `(0, ∞)`: strict on both sides.
#thales_prove "b.ts" "idf" "posOpen" :=
  ts.forall(ts.binder["a"](ts.number,
      ts.lower["<"](ts.fnum[0]), ts.upper["<"](ts.fnum[Infinity]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  }

-- `(-∞, 1]`: a strict -∞ floor.
#thales_prove "b.ts" "idf" "negOpen" :=
  ts.forall(ts.binder["a"](ts.number,
      ts.lower["<"](ts.fnum[-Infinity]), ts.upper["<="](ts.fnum[1]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  }

-- `[-∞, ∞]`: closed infinities, so the guards exclude only NaN.
#thales_prove "b.ts" "idf" "closedInf" :=
  ts.forall(ts.binder["a"](ts.number,
      ts.lower["<="](ts.fnum[-Infinity]), ts.upper["<="](ts.fnum[Infinity]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  }

-- What the infinity guards admit, decided on the comparisons the
-- hypotheses use: a strict bound rejects its own infinity and NaN; a
-- closed bound admits its infinity and still rejects NaN. Core names
-- neither special value, so NaN is constructed the way floatInf is.
private def floatNaN : Float := 0.0 / 0.0

example : ¬ (floatInf < floatInf) := by decide
example : ¬ (floatNaN < floatInf) := by decide
example : floatInf ≤ floatInf := by decide
example : ¬ (floatNaN ≤ floatInf) := by decide
example : ¬ (-floatInf < -floatInf) := by decide
example : ¬ (-floatInf < floatNaN) := by decide
example : -floatInf ≤ -floatInf := by decide
example : ¬ (-floatInf ≤ floatNaN) := by decide
-- A strict infinity bound still admits finite doubles.
example : (12345.0 : Float) < floatInf := by decide
example : -floatInf < (-12345.0 : Float) := by decide

-- Signed zeros. An interval excludes an endpoint by adjacency in an ordering
-- where -0 sits below 0, which IEEE comparison cannot express; these pin what
-- each spelling's guard must admit, so it stays a superset of the refuter's
-- domain rather than a subset.

-- `(-0, 1]` admits 0, and lowers relaxed, so its guard keeps it.
example : (-0.0 : Float) ≤ 0.0 ∧ (0.0 : Float) ≤ 1.0 := by decide
-- `[-1, 0)` admits -0, and lowers relaxed, so its guard keeps it.
example : (-1.0 : Float) ≤ -0.0 ∧ (-0.0 : Float) ≤ 0.0 := by decide
-- `(0, 1]` and `[-1, -0)` admit neither zero, so both stay strict: a strict
-- comparison against either zero already rejects both.
example : ¬ ((0.0 : Float) < 0.0) ∧ ¬ ((-0.0 : Float) < 0.0) := by decide
example : ¬ ((-0.0 : Float) < -0.0) ∧ ¬ ((0.0 : Float) < -0.0) := by decide
