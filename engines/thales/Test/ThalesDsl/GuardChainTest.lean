import ThalesDsl.Prove

open ThalesDsl Lean

ts_def "idf" := ts.fn(ts.param["a"](ts.number)) : ts.number {
  ts.return(ts.id["a"])
}

-- The shape elabProp builds for a guard: the guard's evaluation equals
-- `pure true`, as a hypothesis in front of the conclusion.
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.imp(ts.binop[">"](ts.num[1], ts.num[0])) {
    ts.istrue(ts.binop[">"](ts.num[2], ts.num[0]))
  })
  match (← elabProp [] p).prop with
  | `(($_ = pure true) → $_ = pure true) => return true
  | _ => return false

-- A chain threads hypotheses in guard order, outermost first.
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.imp(ts.binop[">"](ts.num[1], ts.num[0])) {
    ts.imp(ts.binop[">"](ts.num[2], ts.num[0])) {
      ts.istrue(ts.binop[">"](ts.num[3], ts.num[0]))
    }
  })
  match (← elabProp [] p).prop with
  | `(($_ = pure true) → ($_ = pure true) → $_ = pure true) => return true
  | _ => return false

-- A guard does not cost the decide rung: the guarded prop of a bounded
-- domain is still all-bounded, with the domain size of its binders.
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {
    ts.imp(ts.binop[">="](ts.id["x"], ts.num[1])) {
      ts.istrue(ts.binop[">="](ts.call["idf"](ts.id["x"]), ts.num[1]))
    }
  })
  let ep ← elabProp [] p
  return ep.allBounded && ep.domainSize == 10

-- What the hypothesis form admits, decided on the semantics the guards
-- use. A thrown guard fails `= pure true` exactly like a false one, so
-- the prover reads both as vacuous truth. The refuter diverges on the
-- thrown case: the same throw escapes its `fc.pre(bool(...))` discard as
-- a `threw` issue (SZS Error). That divergence is deliberate and safe —
-- an Error can never contradict a Theorem — and pinned here plus in
-- pabst's runtime tests rather than left latent.
example : ¬ ((pure false : TsM Bool) = pure true) := by decide
example : ¬ ((TsM.throw (.error "boom") : TsM Bool) = pure true) := by decide
