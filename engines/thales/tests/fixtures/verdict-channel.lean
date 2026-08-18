import ThalesDsl

-- Two healthy stub commands (no structured property yet): each must yield
-- exactly one NotTried verdict line.
#thales_prove "add.ts" "add" "forall (a b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) }"
#thales_prove "add.ts" "sub" "forall (a: int ∈ [0, 10)) { sub(a, a) ≡ 0 }"

-- Deliberate elaboration failure: the property calls a function with no
-- registered model. The failure must be contained to this command's verdict
-- line and must not abort the file.
#thales_prove "add.ts" "bad" "forall (a: int ∈ [0, 10)) { bad(a) ≡ 0 }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["bad"](ts.id["a"]), ts.num[0])
  }

-- An opaque node in the formula is dependence on an unmapped construct,
-- contained to this command's verdict line.
#thales_prove "add.ts" "opq" "forall (a: int ∈ [0, 10)) { opq(a) ≡ 0 }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.opaque["YieldExpression"](3, 14), ts.num[0])
  }

-- A command after the failures proves later commands still report.
#thales_prove "add.ts" "tail" "forall (a: int ∈ [0, 10)) { tail(a) ≡ a }"

-- A call to a declaration that failed on an unmapped construct is
-- Inappropriate for the annotation, not an engine error.
ts_def "aw" := ts.opaque["AwaitExpression"](30, 3)

#thales_prove "add.ts" "viaAw" "forall (a: int ∈ [0, 10)) { aw(a) >= 0 }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10))) {
    ts.istrue(ts.binop[">="](ts.call["aw"](ts.id["a"]), ts.num[0]))
  }
