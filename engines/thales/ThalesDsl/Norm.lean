import Lean
import ThalesDsl.NormAttr
import ThalesDsl.TsM

/-! The `thales_norm` simp set: normalization lemmas that strip TsM's
monadic wrapping from pure-looking goals, leaving bare Int arithmetic
for the closers. Model definitions join the set at creation
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

/-- Open bounded ∀s so the closers see the inequalities. -/
@[thales_norm] theorem ballIco_iff (lo hi : Int) (p : Int → Prop) :
    ballIco lo hi p ↔ ∀ x : Int, lo ≤ x → x < hi → p x :=
  Iff.rfl

end ThalesDsl
