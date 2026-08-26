import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- The recursion limit is not the heartbeat budget: a rung that blows it has
-- failed, but the annotation has not. Each limit below is tuned to land in
-- one phase; a toolchain bump can shift the windows and force a retune.
@[js_norm, grind]
def TsModel.bump (x : JsNumber) : JsM JsNumber := do
  return x + 1

-- Blown inside proof search: normalization cannot even unfold the model, so
-- the ladder runs out and reports the goal it was left with.
set_option maxRecDepth 15 in
#thales_prove "recdepth.ts" "bump" "fixed" :=
  ∀ (x : Int), TsModel.bump (Float.ofInt x) = pure (Float.ofInt x)

-- Blown while the property is still being built: the binder spine is deep
-- enough that recovering it exhausts the limit before any rung runs, which
-- is an honest elaboration failure.
set_option linter.unusedVariables false in
set_option maxRecDepth 25 in
#thales_prove "recdepth.ts" "bump" "deepSpine" :=
  ballIco 0 1 fun a =>
    ballIco 0 1 fun b =>
      ballIco 0 1 fun c =>
        ballIco 0 1 fun d =>
          ballIco 0 1 fun e =>
            ballIco 0 1 fun f =>
              TsModel.bump (Float.ofInt a) = pure (Float.ofInt a + 1)

-- Containment: the next annotation still runs, at the default limit.
#thales_prove "recdepth.ts" "bump" "grows" :=
  ballIco 0 10 fun x =>
    ((do
          return Float.lt (Float.ofInt x) (← TsModel.bump (Float.ofInt x))) :
        JsM Bool) =
      pure true
