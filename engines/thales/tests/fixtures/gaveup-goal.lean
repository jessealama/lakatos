import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- An honest exhaustion: bump(x) = x is false for every x, but the prover
-- does not hunt witnesses in unbounded domains — the ladder runs out and
-- the verdict carries the goal that stumped it.
@[js_norm, grind]
def TsModel.bump (x : JsNumber) : JsM JsNumber := do
  return x + 1

#thales_prove "gaveup.ts" "bump" "fixed" :=
  ∀ (x : Int), TsModel.bump (Float.ofInt x) = pure (Float.ofInt x)

-- A bounded domain far too large for either decide tier. Both starve, and
-- ballIco_iff then hands the symbolic rungs the same property in hypothesis
-- form, so the annotation reports an unsolved goal rather than a bare
-- timeout. The residual names the Float fact that would have closed it.
@[js_norm, grind]
def TsModel.wide (x : JsNumber) : JsM JsNumber := do
  return x * x

#thales_prove "wide.ts" "wide" "nonneg" :=
  ballIco 0 100000000 fun x =>
    ((do
          return Float.le 0 (← TsModel.wide (Float.ofInt x))) :
        JsM Bool) =
      pure true
