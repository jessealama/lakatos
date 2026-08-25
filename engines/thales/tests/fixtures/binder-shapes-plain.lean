import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

@[js_norm, grind]
def TsModel.ident (x : JsNumber) : JsM JsNumber := do
  return x

-- negative lo: the witness must be the range's own floor, not 0
#thales_prove "binder-shapes-plain.lean" "ident" "negativeFloor" :=
  ballIco (-3) 3 fun x =>
    ((pure (Float.le 0 (Float.ofInt x)) : JsM Bool) = pure true)

-- unbounded int: false but unsearchable, ships GaveUp with no witness
#thales_prove "binder-shapes-plain.lean" "ident" "unboundedFalse" :=
  ∀ (x : Int), TsModel.ident (Float.ofInt x) = pure 0

-- nat shape: unbounded, hypothesis stays in the goal
#thales_prove "binder-shapes-plain.lean" "ident" "natShaped" :=
  ∀ (n : Int), 0 ≤ n →
    ((pure (Float.le 0 (Float.ofInt n)) : JsM Bool) = pure true)

-- a ranged binder over an unbounded one: the spine keeps both, so nothing
-- is bounded and the decide rungs stand down
#thales_prove "binder-shapes-plain.lean" "ident" "mixedSpine" :=
  ballIco 0 3 fun x =>
    ∀ (n : Int), TsModel.ident (Float.ofInt n) = pure (Float.ofInt x)
