import ThalesDsl.Model

open ThalesDsl

-- Each core constructor of the pure-arithmetic slice, elaborated by ts_def
-- into a computable model under TsModel.*.

-- ts.num literal (and zero-parameter functions).
ts_def "answer" := ts.fn() : ts.number { ts.return(ts.num[42]) }
#guard decide (TsModel.answer = (pure 42.0 : TsM Float))

-- Negative literals.
ts_def "minus3" := ts.fn() : ts.number { ts.return(ts.num[-3]) }
#guard decide (TsModel.minus3 = (pure (-3.0) : TsM Float))

-- ts.id parameter references and ts.binop "+".
ts_def "add" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["a"], ts.id["b"]))
}
#guard decide (TsModel.add 2.0 3.0 = (pure 5.0 : TsM Float))

-- ts.binop "-" and "*".
ts_def "sub" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["-"](ts.id["a"], ts.id["b"]))
}
#guard decide (TsModel.sub 2.0 5.0 = (pure (-3.0) : TsM Float))

ts_def "sq" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}
#guard decide (TsModel.sq (-4.0) = (pure 16.0 : TsM Float))

-- ts.binop "/" — total IEEE division: finite quotients, signed infinities
-- at zero divisors, NaN at 0/0.
ts_def "ratio" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["/"](ts.id["a"], ts.id["b"]))
}
#guard decide (TsModel.ratio 7.0 2.0 = (pure 3.5 : TsM Float))
#guard decide (TsModel.ratio 1.0 0.0 = (pure (1.0 / 0.0) : TsM Float))
#guard decide (TsModel.ratio (-1.0) 0.0 = (pure (-(1.0 / 0.0)) : TsM Float))
#guard decide (TsModel.ratio 0.0 0.0 = (pure (0.0 / 0.0) : TsM Float))

-- ts.call: models call previously registered models.
ts_def "twice" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.call["add"](ts.id["x"], ts.id["x"]))
}
#guard decide (TsModel.twice 7.0 = (pure 14.0 : TsM Float))

-- Nested expressions compose.
ts_def "affine" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.binop["*"](ts.num[2], ts.id["x"]), ts.num[1]))
}
#guard decide (TsModel.affine 10.0 = (pure 21.0 : TsM Float))

-- `≡` is SameValue and `===` is IEEE strict equality. They disagree on
-- exactly two families of values, and both disagreements are pinned here
-- so the two spellings can never silently re-converge.

-- A body yields a number, so `===` cannot appear at the top of one; the
-- SameValue side is pinned through models producing the contested values,
-- and the IEEE side on the primitive `===` lowers to.

-- `x * 0` is NaN at the infinities, +0 at positive x and -0 at negative x.
ts_def "zeroOver" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.num[0]))
}

-- SameValue, via Lean's `=` on TsM Float, which is what `ts.eq` (`≡`)
-- elaborates to: NaN *is* the same value as itself.
#guard decide (TsModel.zeroOver (1.0 / 0.0) = TsModel.zeroOver (1.0 / 0.0))
-- SameValue: +0 and -0 are different values.
#guard decide (¬ (TsModel.zeroOver 1.0 = TsModel.zeroOver (-1.0)))

-- IEEE, via `Float.beq`, which is what evalExpr lowers `===` to: NaN is
-- not strictly equal to itself, and +0 is strictly equal to -0. Both
-- disagree with SameValue above, so the two spellings cannot re-converge.
#guard decide (Float.beq (0.0 / 0.0) (0.0 / 0.0) = false)
#guard decide (Float.beq 0.0 (-0.0) = true)
