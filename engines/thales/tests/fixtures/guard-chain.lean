import ThalesDsl

-- Guard-chain implications: each guard is a hypothesis in front of the
-- conclusion, so the decide rung settles the property over exactly the
-- guarded slice of the domain.
ts_def "idg" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.id["x"])
}

-- True on the guarded slice: id keeps the floor its guard grants.
#thales_prove "gc.ts" "idg" "forall (x: int ∈ [0, 10)) { x >= 1 → idg(x) >= 1 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.imp(ts.binop[">="](ts.id["x"], ts.num[1])) {
      ts.istrue(ts.binop[">="](ts.call["idg"](ts.id["x"]), ts.num[1]))
    }
  }

-- A two-guard chain, right-nested in guard order.
#thales_prove "gc.ts" "idg" "forall (x: int ∈ [0, 10)) { x >= 1 → x >= 2 → idg(x) >= 2 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.imp(ts.binop[">="](ts.id["x"], ts.num[1])) {
      ts.imp(ts.binop[">="](ts.id["x"], ts.num[2])) {
        ts.istrue(ts.binop[">="](ts.call["idg"](ts.id["x"]), ts.num[2]))
      }
    }
  }

-- A constant-false guard: any conclusion holds vacuously.
#thales_prove "gc.ts" "idg" "forall (x: int ∈ [0, 10)) { 0 > 1 → idg(x) < 0 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.imp(ts.binop[">"](ts.num[0], ts.num[1])) {
      ts.istrue(ts.binop["<"](ts.call["idg"](ts.id["x"]), ts.num[0]))
    }
  }

-- A guard under a number binder — the target shape of guarded
-- monotonicity. Nothing here is bounded, so this composition reaches the
-- symbolic rungs: the guard hypothesis feeds the search, which closes the
-- identity case outright.
#thales_prove "gc.ts" "idg" "forall (x: number ∈ (0, ∞)) { x >= 1 → idg(x) >= 1 }" :=
  ts.forall(ts.binder["x"](ts.number, ts.lower["<"](ts.fnum[0]), ts.upper["<"](ts.fnum[Infinity]))) {
    ts.imp(ts.binop[">="](ts.id["x"], ts.num[1])) {
      ts.istrue(ts.binop[">="](ts.call["idg"](ts.id["x"]), ts.num[1]))
    }
  }

-- False on the guarded slice, and the witness respects the guard: the
-- first counterexample is the first x satisfying x >= 5, never x = 0.
#thales_prove "gc.ts" "idg" "forall (x: int ∈ [0, 10)) { x >= 5 → idg(x) <= 4 }" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.imp(ts.binop[">="](ts.id["x"], ts.num[5])) {
      ts.istrue(ts.binop["<="](ts.call["idg"](ts.id["x"]), ts.num[4]))
    }
  }
