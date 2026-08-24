import ThalesDsl

open ThalesDsl

-- The normalization lemmas settle the goal shapes the ladder's generic
-- stage faces: model-shaped bind chains reduced to bare Int arithmetic.
example (x : Int) :
    (pure x >>= fun a => pure 1 >>= fun b => pure (a + b) : TsM Int) =
      (pure (x + 1) : TsM Int) := by
  simp only [tsm_pure_bind]

example : ∀ x : Int,
    (pure x >>= fun a => pure 2 >>= fun b => pure (a * b) : TsM Int) =
      (pure x >>= fun a => pure x >>= fun b => pure (a + b) : TsM Int) := by
  intro x
  simp only [tsm_pure_bind, tsm_pure_inj]
  omega

-- Boolean islands: the comparison under pure discharges to its Prop.
example (x : Int) (h : 0 ≤ x) :
    (pure x >>= fun a => pure 0 >>= fun b => pure (decide (a ≥ b)) : TsM Bool) =
      pure true := by
  simp only [tsm_pure_bind, tsm_pure_inj, decide_eq_true_eq]
  omega

-- Bounded ∀s open up for the arithmetic closers.
example : ballIco 0 5 (fun x => x + 1 > x) := by
  simp only [ballIco_iff]
  omega

-- A ts_def model unfolds by its equations (attribute-based inclusion in
-- the simp set is exercised end to end by the ladder fixtures).
ts_def "dblNorm" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["*"](ts.id["x"], ts.num[2]))
}

example (x : Float) : TsModel.dblNorm x = (pure (x * 2) : TsM Float) := by
  simp only [TsModel.dblNorm, tsm_pure_bind]

-- Division sheds its monadic wrapping like the other arithmetic operators.
ts_def "halveNorm" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["/"](ts.id["x"], ts.num[2]))
}

example (x : Float) : TsModel.halveNorm x = (pure (x / 2) : TsM Float) := by
  simp only [TsModel.halveNorm, tsm_pure_bind]

-- Remainder sheds its monadic wrapping like the other arithmetic operators.
ts_def "remNorm" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.binop["%"](ts.id["x"], ts.num[7]))
}

example (x : Float) :
    TsModel.remNorm x = (pure (ThalesDsl.FloatOps.tsRem x 7) : TsM Float) := by
  simp only [TsModel.remNorm, tsm_pure_bind]

-- Subtraction normalizes to addition of the negation: the first binary64
-- fact in the set. Driving it through `thales_norm` rather than the lemma
-- name pins membership, not just the proof.
ts_def "diffNorm" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {
  ts.return(ts.binop["-"](ts.id["a"], ts.id["b"]))
}

example (a b : Float) : TsModel.diffNorm a b = (pure (a + (-b)) : TsM Float) := by
  simp only [TsModel.diffNorm, thales_norm]

-- Unary minus sheds its wrapping, and double negation strips away:
-- float_neg_neg is in the set now that an operator can write it.
ts_def "negNorm" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.unop["-"](ts.unop["-"](ts.id["x"])))
}

example (x : Float) : TsModel.negNorm x = (pure x : TsM Float) := by
  simp only [TsModel.negNorm, thales_norm]
