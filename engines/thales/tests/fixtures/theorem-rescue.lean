import ThalesDsl

-- A bounded domain decide cannot afford, over a goal the generic rung
-- proves for every integer: rung-1 exhaustion must fall through, not
-- consume the annotation.
ts_def "dbl" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.num[2]))
}

set_option thales.heartbeats 20000 in
#thales_prove "rescue.ts" "dbl" "forall (x: int ∈ [0, 1000000)) { dbl(x) === x + x }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 1000000))) {
    ts.eq(ts.call["dbl"](ts.id["x"]), ts.binop["+"](ts.id["x"], ts.id["x"]))
  }
