import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- Nonlinear arithmetic over an unbounded domain, so no rung can settle it:
-- nothing to enumerate, and associativity genuinely fails under binary64
-- rounding, so no theory upgrade can ever promote it to Theorem. The grind
-- rung's residual goal is what this fixture pins.
@[js_norm, grind]
def TsModel.mul (x y : JsNumber) : JsM JsNumber := do
  return x * y

#thales_prove "grind.ts" "mul" "associates" :=
  ∀ (x : Int),
    ∀ (y : Int),
      ∀ (z : Int),
        ((do
              return (← TsModel.mul (← TsModel.mul (Float.ofInt x) (Float.ofInt y))
                  (Float.ofInt z))) :
            JsM JsNumber) =
          ((do
                return (← TsModel.mul (Float.ofInt x)
                    (← TsModel.mul (Float.ofInt y) (Float.ofInt z)))) :
              JsM JsNumber)
