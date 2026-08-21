import ThalesDsl

-- An honest exhaustion: bump(x) = x is false for every x, but the prover
-- does not hunt witnesses in unbounded domains — the ladder runs out and
-- the verdict carries the goal that stumped it.
ts_def "bump" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["+"](ts.id["x"], ts.num[1]))
}

#thales_prove "gaveup.ts" "bump" "forall (x: int) { bump(x) === x }" :=
  ts.forall(ts.binder["x"](ts.int)) {
    ts.eq(ts.call["bump"](ts.id["x"]), ts.id["x"])
  }

-- A bounded domain far too large for either decide tier. Both starve, and
-- ballIco_iff then hands the symbolic rungs the same property in hypothesis
-- form, so the annotation reports an unsolved goal rather than a bare
-- timeout. The residual names the Float fact that would have closed it.
ts_def "wide" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.id["x"]))
}
#thales_prove "wide.ts" "wide" "nonneg" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 100000000))) {
    ts.istrue(ts.binop[">="](ts.call["wide"](ts.id["x"]), ts.num[0]))
  }
