import ThalesDsl

-- The recursion limit is not the heartbeat budget: a rung that blows it has
-- failed, but the annotation has not. Each limit below is tuned to land in
-- one phase; a toolchain bump can shift the windows and force a retune.
ts_def "bump" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["x"], ts.num[1]))
}

-- Blown inside proof search: the ladder runs out and reports the goal.
set_option maxRecDepth 25 in
#thales_prove "recdepth.ts" "bump" "forall (x: int) { bump(x) === x }" :=
  ts.forall(ts.binder["x"](ts.int)) {
    ts.eq(ts.call["bump"](ts.id["x"]), ts.id["x"])
  }

-- Blown while the property is still being built: an honest elaboration failure.
set_option maxRecDepth 14 in
#thales_prove "recdepth.ts" "bump" "forall (x: int) { bump(x) === x }" :=
  ts.forall(ts.binder["x"](ts.int)) {
    ts.eq(ts.call["bump"](ts.id["x"]), ts.id["x"])
  }

-- Containment: the next annotation still runs, at the default limit.
#thales_prove "recdepth.ts" "bump" "forall (x: int ∈ [0, 10)) { bump(x) > x }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.istrue(ts.binop[">"](ts.call["bump"](ts.id["x"]), ts.id["x"]))
  }
