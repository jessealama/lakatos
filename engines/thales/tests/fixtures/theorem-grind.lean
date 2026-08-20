import ThalesDsl

-- Goals past omega's reach: nonlinear arithmetic over unbounded domains.
-- The ladder's grind rung closes these after simp/omega gives up.
ts_def "mul" := ts.fn(ts.param["x"](ts.number), ts.param["y"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["y"]))
}

#thales_prove "grind.ts" "mul" "forall (x: int, y: int) { mul(x, y) === mul(y, x) }" :=
  ts.forall(ts.binder["x"](ts.int), ts.binder["y"](ts.int)) {
    ts.eq(ts.call["mul"](ts.id["x"], ts.id["y"]), ts.call["mul"](ts.id["y"], ts.id["x"]))
  }
