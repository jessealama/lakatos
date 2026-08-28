import ThalesDsl

open ThalesDsl Js Js.Number

-- The normalization lemmas settle the goal shapes the ladder's generic
-- stage faces: model-shaped bind chains reduced to bare Int arithmetic.
example (x : Int) :
    (pure x >>= fun a => pure 1 >>= fun b => pure (a + b) : JsM Int) =
      (pure (x + 1) : JsM Int) := by
  simp only [jsm_pure_bind]

example : ∀ x : Int,
    (pure x >>= fun a => pure 2 >>= fun b => pure (a * b) : JsM Int) =
      (pure x >>= fun a => pure x >>= fun b => pure (a + b) : JsM Int) := by
  intro x
  simp only [jsm_pure_bind, jsm_pure_inj]
  omega

-- Boolean islands: the comparison under pure discharges to its Prop.
example (x : Int) (h : 0 ≤ x) :
    (pure x >>= fun a => pure 0 >>= fun b => pure (decide (a ≥ b)) : JsM Bool) =
      pure true := by
  simp only [jsm_pure_bind, jsm_pure_inj, decide_eq_true_eq]
  omega

-- Bounded ∀s open up for the arithmetic closers.
example : ballIco 0 5 (fun x => x + 1 > x) := by
  simp only [ballIco_iff]
  omega

-- An emitted model unfolds by its equations (attribute-based inclusion in
-- the simp set is exercised end to end by the ladder fixtures).
@[js_norm, grind]
def TsModel.dblNorm (x : JsNumber) : JsM JsNumber := do
  return x * 2

example (x : Float) : TsModel.dblNorm x = (pure (x * 2) : JsM Float) := by
  simp only [TsModel.dblNorm, jsm_pure_bind]

-- Division sheds its monadic wrapping like the other arithmetic operators.
@[js_norm, grind]
def TsModel.halveNorm (x : JsNumber) : JsM JsNumber := do
  return x / 2

example (x : Float) : TsModel.halveNorm x = (pure (x / 2) : JsM Float) := by
  simp only [TsModel.halveNorm, jsm_pure_bind]

-- Remainder sheds its monadic wrapping like the other arithmetic operators.
@[js_norm, grind]
def TsModel.remNorm (x : JsNumber) : JsM JsNumber := do
  return Number.FloatOps.tsRem x 7

example (x : Float) :
    TsModel.remNorm x = (pure (Js.Number.FloatOps.tsRem x 7) : JsM Float) := by
  simp only [TsModel.remNorm, jsm_pure_bind]

-- Subtraction normalizes to addition of the negation: the first binary64
-- fact in the set. Driving it through `js_norm` rather than the lemma
-- name pins membership, not just the proof.
@[js_norm, grind]
def TsModel.diffNorm (a b : JsNumber) : JsM JsNumber := do
  return a - b

example (a b : Float) : TsModel.diffNorm a b = (pure (a + (-b)) : JsM Float) := by
  simp only [TsModel.diffNorm, js_norm]

-- Unary minus sheds its wrapping, and double negation strips away:
-- float_neg_neg is in the set now that an operator can write it.
@[js_norm, grind]
def TsModel.negNorm (x : JsNumber) : JsM JsNumber := do
  return - -x

example (x : Float) : TsModel.negNorm x = (pure x : JsM Float) := by
  simp only [TsModel.negNorm, js_norm]

-- A throwing statement short-circuits the rest of a constructor, so no
-- successful construction survives a guard it triggered.
example (e : JsError) (k : Unit → JsM Nat) (n : Nat) :
    ((do throw e; k ()) : JsM Nat) = .ok n → False := by
  grind

-- The bounds a class binder gets, from the guard alone.
example (x : Float) (h : Float.isFinite x = true) : -floatInf < x ∧ x < floatInf := by
  grind
