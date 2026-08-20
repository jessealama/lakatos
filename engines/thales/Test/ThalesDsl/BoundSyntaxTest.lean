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
