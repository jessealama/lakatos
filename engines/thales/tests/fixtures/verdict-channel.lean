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

-- An opaque node reaching expression elaboration always fails, contained
-- to this command's verdict line.
#thales_prove "add.ts" "opq" "forall (a: int ∈ [0, 10)) { opq(a) ≡ 0 }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.opaque["YieldExpression"](3, 14), ts.num[0])
  }

-- A command after the failures proves later commands still report.
#thales_prove "add.ts" "tail" "forall (a: int ∈ [0, 10)) { tail(a) ≡ a }"
