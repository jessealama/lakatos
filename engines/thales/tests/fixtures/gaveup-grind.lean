import ThalesDsl

-- Nonlinear arithmetic over an unbounded domain, so no rung can settle it:
-- nothing to enumerate, and no binary64 multiplication theory to reason
-- with. Commutativity of multiplication is the residual, and the first
-- entry on the theory worklist.
ts_def "mul" := ts.fn(ts.param["x"](ts.number), ts.param["y"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["y"]))
}

#thales_prove "grind.ts" "mul" "forall (x: int, y: int) { mul(x, y) === mul(y, x) }" :=
  ts.forall(ts.binder["x"](ts.int), ts.binder["y"](ts.int)) {
    ts.eq(ts.call["mul"](ts.id["x"], ts.id["y"]), ts.call["mul"](ts.id["y"], ts.id["x"]))
  }
