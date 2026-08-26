import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- Unbounded domains, so there is nothing to enumerate, and the bodies are
-- binary64, for which vanilla Lean carries no arithmetic theory. Every one
-- of these is true; the symbolic rungs cannot show it yet. The residual
-- goal each verdict carries names the fact that would close it, which is
-- how the theory worklist is discovered rather than guessed.
@[js_norm, grind]
def TsModel.dbl (x : JsNumber) : JsM JsNumber := do
  return x * 2

#thales_prove "generic.ts" "dbl" "doubles" :=
  ∀ (x : Int),
    TsModel.dbl (Float.ofInt x) = pure (Float.ofInt x + Float.ofInt x)

-- A nat binder carries its nonnegativity hypothesis into the residual.
#thales_prove "generic.ts" "dbl" "grows" :=
  ∀ (x : Int), 0 ≤ x →
    ((do
          return Float.le (Float.ofInt x) (← TsModel.dbl (Float.ofInt x))) :
        JsM Bool) =
      pure true

-- Mixed binders: any unbounded binder sidelines decide for the whole prop.
#thales_prove "generic.ts" "dbl" "mixed" :=
  ∀ (x : Int),
    ballIco 0 10 fun y =>
      ((do
            return Float.le (Float.ofInt x + Float.ofInt x)
              ((← TsModel.dbl (Float.ofInt x)) + Float.ofInt y)) :
          JsM Bool) =
        pure true
