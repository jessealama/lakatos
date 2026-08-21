import ThalesDsl

-- Unbounded domains, so there is nothing to enumerate, and the bodies are
-- binary64, for which vanilla Lean carries no arithmetic theory. Every one
-- of these is true; the symbolic rungs cannot show it yet. The residual
-- goal each verdict carries names the fact that would close it, which is
-- how the theory worklist is discovered rather than guessed.
ts_def "dbl" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.num[2]))
}

#thales_prove "generic.ts" "dbl" "forall (x: int) { dbl(x) === x + x }" :=
  ts.forall(ts.binder["x"](ts.int)) {
    ts.eq(ts.call["dbl"](ts.id["x"]), ts.binop["+"](ts.id["x"], ts.id["x"]))
  }

-- A nat binder carries its nonnegativity hypothesis into the residual.
#thales_prove "generic.ts" "dbl" "forall (x: nat) { dbl(x) >= x }" :=
  ts.forall(ts.binder["x"](ts.nat)) {
    ts.istrue(ts.binop[">="](ts.call["dbl"](ts.id["x"]), ts.id["x"]))
  }

-- Mixed binders: any unbounded binder sidelines decide for the whole prop.
#thales_prove "generic.ts" "dbl" "forall (x: int, y: int ∈ [0, 10)) { dbl(x) + y >= x + x }" :=
  ts.forall(ts.binder["x"](ts.int), ts.binder["y"](ts.int, ts.range(0, 10))) {
    ts.istrue(ts.binop[">="](
      ts.binop["+"](ts.call["dbl"](ts.id["x"]), ts.id["y"]),
      ts.binop["+"](ts.id["x"], ts.id["x"])))
  }
