import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- A domain the prover cannot afford: the clamped per-annotation budget
-- makes the attempt time out, contained as a Timeout verdict — and the
-- next annotation still runs with a fresh budget.
@[js_norm, grind]
def TsModel.slow (x : JsNumber) : JsM JsNumber := do
  return x * x

@[js_norm, grind]
def TsModel.add (x y : JsNumber) : JsM JsNumber := do
  return x + y

set_option thales.heartbeats 1 in
#thales_prove "stuck.ts" "slow" "nonneg" :=
  ballIco 0 1000000 fun x =>
    ((do
          return Float.le 0 (← TsModel.slow (Float.ofInt x))) :
        JsM Bool) =
      pure true

#thales_prove "stuck.ts" "add" "zeroNeutral" :=
  ballIco 0 10 fun x =>
    TsModel.add (Float.ofInt x) 0 = pure (Float.ofInt x)

-- Kernel-side exhaustion is still budget exhaustion: the kernel's own
-- deterministic timeout fires while the elaborator still has heartbeats,
-- and the generic rung cannot rescue a nonlinear goal. The domain is put
-- past the evaluation cap so the tier that would otherwise settle it — and
-- that no budget can interrupt — stands down.
set_option thales.maxEvaluatedElements 1000 in
set_option thales.heartbeats 50000 in
#thales_prove "stuck.ts" "slow" "nonnegKernel" :=
  ballIco 0 1000000 fun x =>
    ((do
          return Float.le 0 (← TsModel.slow (Float.ofInt x))) :
        JsM Bool) =
      pure true

-- Lean reads maxHeartbeats 0 as "no limit", so a zero budget is clamped to
-- the smallest real one rather than passed through; the reason names the
-- budget that actually ran.
set_option thales.heartbeats 0 in
#thales_prove "stuck.ts" "slow" "nonnegZeroBudget" :=
  ballIco 0 1000000 fun x =>
    ((do
          return Float.le 0 (← TsModel.slow (Float.ofInt x))) :
        JsM Bool) =
      pure true
