import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- A residual site: what an unmodelable expression becomes in a model. The
-- opaque asserts nothing about its value and cannot be evaluated, so a
-- proof that forces one cannot close — and one that never reaches it is
-- unaffected.
/-- 'Math.log' is not supported -/
noncomputable opaque TsModel.f.residual_1 : (x : JsNumber) → JsM JsNumber

@[js_norm, grind]
noncomputable def TsModel.f (x : JsNumber) : JsM JsNumber := do
  if Float.lt x 0 then
    return (← TsModel.f.residual_1 x)
  return x

-- Off the path on a bounded domain: every element takes the other arm, so
-- the branch reduces in the kernel without the opaque ever being forced.
#thales_prove "residual.ts" "f" "offPath" :=
  ballIco 0 5 fun x =>
    ((do return Float.le 0 (← TsModel.f (Float.ofInt x))) : JsM Bool) = pure true

-- Off the path with an unbounded binder: the guard refutes the arm holding
-- the site, which is what the `ite` splitters buy.
#thales_prove "residual.ts" "f" "unboundedOffPath" :=
  ∀ (x : JsNumber), Float.le 0 x = true →
    ((do return Float.le 0 (← TsModel.f x)) : JsM Bool) = pure true

-- On the path: the guard selects the arm holding the site, so the only
-- failing leaf is the one forcing it and the verdict names its construct.
#thales_prove "residual.ts" "f" "onPath" :=
  ∀ (x : JsNumber), Float.lt x 0 = true →
    ((do return Float.le 0 (← TsModel.f x)) : JsM Bool) = pure true

-- A site is not an excuse: the arm the property does take fails on its own
-- arithmetic, and that failure is the engine's to report, not the model's.
@[js_norm, grind]
noncomputable def TsModel.g (x : JsNumber) : JsM JsNumber := do
  if Float.lt x 0 then
    return (← TsModel.f.residual_1 x)
  return x + 1

#thales_prove "residual.ts" "g" "arithmeticArm" :=
  ∀ (x : JsNumber), Float.le 0 x = true →
    ((do return Float.le x (← TsModel.g x)) : JsM Bool) = pure true
