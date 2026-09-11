import Js

open Js

/-! A branch whose arm is a monadic term the set cannot see through — an
opaque here, a residual in an artifact — still splits per arm, so the
guard can refute the arm the property never takes. -/

noncomputable opaque residualArm : JsNumber → JsM JsNumber

@[js_norm]
noncomputable def guarded (x : JsNumber) : JsM JsNumber := do
  if Float.lt x 0 then
    return (← residualArm x)
  return x

-- The off-path arm is refuted from the guard; the taken arm is trivial.
example : ∀ (x : JsNumber), Float.le 0 x = true →
    ((do return Float.le 0 (← guarded x)) : JsM Bool) = pure true := by
  intro x hx
  simp only [js_norm]
  grind

-- The split itself, stated as the lemmas say it.
example (c : Bool) (x y : JsM JsNumber) (f : JsNumber → JsM Bool) :
    ((if c = true then x else y) >>= f) =
      if c = true then x >>= f else y >>= f := jsm_ite_bind c x y f
example (c : Bool) (x y z : JsM JsNumber) :
    ((if c = true then x else y) = z) ↔
      ((c = true → x = z) ∧ (c = false → y = z)) := jsm_ite_eq c x y z
