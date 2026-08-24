import ThalesDsl

-- Nonlinear arithmetic over an unbounded domain, so no rung can settle it:
-- nothing to enumerate, and associativity genuinely fails under binary64
-- rounding, so no theory upgrade can ever promote it to Theorem. The grind
-- rung's residual goal is what this fixture pins.
ts_def "mul" := ts.fn(ts.param["x"](ts.number), ts.param["y"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["y"]))
}

#thales_prove "grind.ts" "mul" "forall (x: int, y: int, z: int) { mul(mul(x, y), z) === mul(x, mul(y, z)) }" :=
  ts.forall(ts.binder["x"](ts.int), ts.binder["y"](ts.int), ts.binder["z"](ts.int)) {
    ts.eq(ts.call["mul"](ts.call["mul"](ts.id["x"], ts.id["y"]), ts.id["z"]),
          ts.call["mul"](ts.id["x"], ts.call["mul"](ts.id["y"], ts.id["z"])))
  }
