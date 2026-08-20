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
