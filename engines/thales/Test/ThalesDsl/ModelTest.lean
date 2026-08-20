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
