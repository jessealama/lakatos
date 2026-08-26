import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- A bounded domain the kernel rung cannot afford under a clamped budget:
-- its exhaustion must fall through to a later rung, not consume the
-- annotation.
@[js_norm, grind]
def TsModel.dbl (x : JsNumber) : JsM JsNumber := do
  return x * 2

set_option thales.heartbeats 20000 in
#thales_prove "rescue.ts" "dbl" "doubles" :=
  ballIco 0 1000000 fun x =>
    TsModel.dbl (Float.ofInt x) = pure (Float.ofInt x + Float.ofInt x)
