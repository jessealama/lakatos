import ThalesDsl

-- A domain the prover cannot afford: the clamped per-annotation budget
-- makes the attempt time out, contained as a Timeout verdict — and the
-- next annotation still runs with a fresh budget.
ts_def "slow" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}

ts_def "add" := ts.fn(ts.param["x"](ts.number), ts.param["y"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["x"], ts.id["y"]))
}

set_option thales.heartbeats 1 in
#thales_prove "stuck.ts" "slow" "forall (x: int ∈ [0, 1000000)) { slow(x) >= 0 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 1000000))) {
    ts.istrue(ts.binop[">="](ts.call["slow"](ts.id["x"]), ts.num[0]))
  }

#thales_prove "stuck.ts" "add" "forall (x: int ∈ [0, 10)) { add(x, 0) === x }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["add"](ts.id["x"], ts.num[0]), ts.id["x"])
  }
