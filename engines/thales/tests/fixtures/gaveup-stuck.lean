import ThalesDsl

-- A domain the elaborator cannot afford to evaluate: the clamped heartbeat
-- budget makes decide give up before reaching a truth value, and the
-- failure is contained as a GaveUp verdict, not an artifact failure.
ts_def "slow" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}

set_option maxHeartbeats 1000 in
#thales_prove "stuck.ts" "slow" "forall (x: int ∈ [0, 1000000)) { slow(x) >= 0 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 1000000))) {
    ts.istrue(ts.binop[">="](ts.call["slow"](ts.id["x"]), ts.num[0]))
  }
