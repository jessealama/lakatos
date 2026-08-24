import Lean
import ThalesDsl.FloatFacts
import ThalesDsl.NormAttr
import ThalesDsl.TsM

/-! The `thales_norm` simp set: normalization lemmas that strip TsM's
monadic wrapping from pure-looking goals, leaving bare Int arithmetic
for the closers, plus the binary64 facts `FloatFacts` proves — vanilla
Lean carries no float theory, so a residual goal about `Float` has none
until one lands here. Model definitions join the set at creation
(Model.lean), so goals can unfold them. -/

namespace ThalesDsl

/-- Collapse `pure a >>= f` one bind at a time; definitional on `Except`. -/
@[thales_norm] theorem tsm_pure_bind {α β : Type} (a : α) (f : α → TsM β) :
    (pure a >>= f : TsM β) = f a := rfl

/-- Two pure results are equal exactly when their values are. -/
@[thales_norm] theorem tsm_pure_inj {α : Type} (a b : α) :
    ((pure a : TsM α) = pure b) ↔ a = b :=
  ⟨fun h => Except.ok.inj h, fun h => h ▸ rfl⟩

-- Boolean islands: after tsm_pure_inj, `decide P = true` becomes `P`.
attribute [thales_norm] decide_eq_true_eq

-- Binary64 theory from FloatFacts. Rewriting subtraction away leaves the
-- closers one operator fewer to reason about.
attribute [thales_norm, grind =] ThalesDsl.FloatFacts.float_sub_eq_add_neg

-- Commutativity of `*` and `+`: the monotonicity facts below are keyed on
-- the right-constant orientation only; these equations let grind identify
-- the left-constant spelling with it. Grind-only — a permutative rewrite
-- has no place in a simp set.
attribute [grind =] ThalesDsl.FloatFacts.float_mul_comm
attribute [grind =] ThalesDsl.FloatFacts.float_add_comm

/-- Open bounded ∀s so the closers see the inequalities. Tagged for grind
too: the grind rung shares the normalization knowledge. -/
@[thales_norm, grind =] theorem ballIco_iff (lo hi : Int) (p : Int → Prop) :
    ballIco lo hi p ↔ ∀ x : Int, lo ≤ x → x < hi → p x :=
  Iff.rfl

/-! The four monotonicity facts, restated on `floatInf` so their bound
hypotheses match what number binders emit, and given grind patterns keyed
on the operation terms: whenever both sides of a comparison goal apply
the same operation, the fact instantiates and the guard chain closes by
forward reasoning. -/

/-- Multiplying both sides by a positive finite factor. -/
theorem float_le_mul_of_le {x y c : Float} (h : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < floatInf) :
    Float.le (x * c) (y * c) = true :=
  FloatFacts.float_le_mul_right h h0 hInf

/-- Adding a finite offset to both sides. -/
theorem float_le_add_of_le {x y c : Float} (h : Float.le x y = true)
    (hLo : -floatInf < c) (hHi : c < floatInf) :
    Float.le (x + c) (y + c) = true :=
  FloatFacts.float_le_add_right h hLo hHi

/-- Dividing both sides by a positive finite divisor. -/
theorem float_le_div_of_le {x y c : Float} (h : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < floatInf) :
    Float.le (x / c) (y / c) = true :=
  FloatFacts.float_le_div_right h h0 hInf

/-- Bounds flip under negation: the offset the sub-rewrite negates keeps
its finiteness. -/
theorem float_neg_lo {c : Float} (h : c < floatInf) : -floatInf < -c :=
  FloatFacts.float_neg_bound_lo h

theorem float_neg_hi {c : Float} (h : -floatInf < c) : -c < floatInf :=
  FloatFacts.float_neg_bound_hi h

/-! A finite binder bound reaches the infinity hypotheses through one
ground comparison: transitivity chains `c < 1000` with `1000 < floatInf`,
and the ground link evaluates away during grind preprocessing. The
infinity endpoint is fixed in each statement so the binder-emitted
comparison alone determines the instantiation. -/

theorem float_lt_inf_of_lt {a b : Float} (h : a < b) (hb : b < floatInf) :
    a < floatInf :=
  FloatFacts.float_lt_trans h hb

theorem float_lt_inf_of_le {a b : Float} (h : a ≤ b) (hb : b < floatInf) :
    a < floatInf :=
  FloatFacts.float_lt_of_le_of_lt h hb

theorem float_gt_neg_inf_of_lt {a b : Float} (ha : -floatInf < a) (h : a < b) :
    -floatInf < b :=
  FloatFacts.float_lt_trans ha h

theorem float_gt_neg_inf_of_le {a b : Float} (ha : -floatInf < a) (h : a ≤ b) :
    -floatInf < b :=
  FloatFacts.float_lt_of_lt_of_le ha h

open Lean Meta Simp in
/-- Evaluates a closed `Float` comparison by reducing its `Decidable`
instance, the way the `decide` tactic does; the kernel recomputes the
reduction when it checks the `Eq.refl` certificate. -/
def reduceGroundFloatCmp (e : Expr) : SimpM Step := do
  if e.hasFVar || e.hasExprMVar then return .continue
  let inst ←
    try synthInstance (mkApp (mkConst ``Decidable) e)
    catch _ => return .continue
  let r ← withAtLeastTransparency .default <| whnf inst
  if r.isAppOf ``Decidable.isTrue then
    return .done { expr := mkConst ``True, proof? := some (← mkEqTrue (← mkDecideProof e)) }
  if r.isAppOf ``Decidable.isFalse then
    let decEqFalse ← mkEq (mkApp2 (mkConst ``Decidable.decide) e inst) (mkConst ``Bool.false)
    let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.false)) decEqFalse
    let pf := mkApp3 (mkConst ``of_decide_eq_false) e inst h
    return .done { expr := mkConst ``False, proof? := some (← mkEqFalse pf) }
  return .continue

/-- A literal factor instantiates a monotonicity fact with ground bound
hypotheses; these evaluate away during normalization. Registered in
`seval` because that is the set grind draws its simprocs from. -/
simproc [seval] reduceFloatLt ((_ : Float) < _) := reduceGroundFloatCmp

simproc [seval] reduceFloatLe ((_ : Float) ≤ _) := reduceGroundFloatCmp

grind_pattern float_le_mul_of_le => x * c, y * c
grind_pattern float_le_add_of_le => x + c, y + c
grind_pattern float_le_div_of_le => x / c, y / c
grind_pattern float_neg_lo => -c
grind_pattern float_neg_hi => -c
grind_pattern float_lt_inf_of_lt => a < b
grind_pattern float_lt_inf_of_le => a ≤ b
grind_pattern float_gt_neg_inf_of_lt => a < b
grind_pattern float_gt_neg_inf_of_le => a ≤ b

end ThalesDsl
