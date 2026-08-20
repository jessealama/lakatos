import ThalesDsl

open ThalesDsl

-- The grind rung shares the normalization knowledge: the thales_norm
-- lemmas and model equations are tagged for grind too, so it can attack
-- goals simp never normalized (a rung-2 window blowout hands grind the
-- original proposition, monadic wrapping intact).

example (x : Int) :
    (pure x >>= fun a => pure 1 >>= fun b => pure (a + b) : TsM Int) =
      (pure (x + 1) : TsM Int) := by
  grind

-- Boolean islands discharge to their Prop for grind as for omega.
example (x : Int) (h : 0 ≤ x) :
    (pure x >>= fun a => pure 0 >>= fun b => pure (decide (a ≥ b)) : TsM Bool) =
      pure true := by
  grind

-- Bounded ∀s open up for grind.
example : ballIco 0 5 (fun x => x + 1 > x) := by
  grind

-- A ts_def model unfolds by its equations under grind.
ts_def "dblGrind" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.num[2]))
}

example (x : Float) : TsModel.dblGrind x = (pure (x * 2) : TsM Float) := by
  grind
