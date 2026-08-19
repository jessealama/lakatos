import ThalesDsl

-- False bounded claims: decide establishes falsity synchronously, and the
-- elaborator searches the bounded domain for the first witness.
ts_def "bump" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["x"], ts.num[1]))
}

-- A false equation: bump adds one, the property says it doesn't.
#thales_prove "cs.ts" "bump" "forall (x: int ∈ [0, 10)) { bump(x) ≡ x }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["bump"](ts.id["x"]), ts.id["x"])
  }

ts_def "sq" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}

-- A false boolean island: fails only at the x = 0 edge.
#thales_prove "cs.ts" "sq" "forall (x: int ∈ [0, 10)) { sq(x) > 0 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.istrue(ts.binop[">"](ts.call["sq"](ts.id["x"]), ts.num[0]))
  }

-- Wrong on purpose: the body never mentions b, so commutativity fails at
-- the first point with a ≠ b — a two-binder witness.
ts_def "comm" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["a"], ts.id["a"]))
}

#thales_prove "cs.ts" "comm" "forall (a b: int ∈ [0, 10)) { comm(a, b) ≡ comm(b, a) }" :=
  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10)), ts.binder["b"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["comm"](ts.id["a"], ts.id["b"]), ts.call["comm"](ts.id["b"], ts.id["a"]))
  }

-- Zero binders: falsity without a witness to extract stays a GaveUp — the
-- envelope's falsified shape requires a non-empty counterexample. Only
-- hand-written artifacts can reach this; Lemma requires a binder.
#thales_prove "cs.ts" "bump" "bump(0) ≡ 0" :=
  ts.forall() {
    ts.eq(ts.call["bump"](ts.num[0]), ts.num[0])
  }
