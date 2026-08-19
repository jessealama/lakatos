import ThalesDsl

-- False bounded claims: the prover must give up with a verdict, not fail
-- the artifact — the built proof term is only kernel-checked after the
-- verdict line would already have been emitted.
ts_def "bump" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["x"], ts.num[1]))
}

-- A false equation: bump adds one, the property says it doesn't.
#thales_prove "gaveup.ts" "bump" "forall (x: int ∈ [0, 10)) { bump(x) ≡ x }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.eq(ts.call["bump"](ts.id["x"]), ts.id["x"])
  }

ts_def "sq" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}

-- A false boolean island: fails only at the x = 0 edge.
#thales_prove "gaveup.ts" "sq" "forall (x: int ∈ [0, 10)) { sq(x) > 0 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.istrue(ts.binop[">"](ts.call["sq"](ts.id["x"]), ts.num[0]))
  }
