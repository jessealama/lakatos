import ThalesDsl.Prove

open ThalesDsl

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
