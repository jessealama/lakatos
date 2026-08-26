import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- False bounded claims: decide establishes falsity synchronously, and the
-- elaborator searches the bounded domain for the first witness.
@[js_norm, grind]
def TsModel.bump (x : JsNumber) : JsM JsNumber := do
  return x + 1

-- A false equation: bump adds one, the property says it doesn't.
#thales_prove "cs.ts" "bump" "fixed" :=
  ballIco 0 10 fun x =>
    TsModel.bump (Float.ofInt x) = pure (Float.ofInt x)

@[js_norm, grind]
def TsModel.sq (x : JsNumber) : JsM JsNumber := do
  return x * x

-- A false boolean island: fails only at the x = 0 edge.
#thales_prove "cs.ts" "sq" "positive" :=
  ballIco 0 10 fun x =>
    ((do
          return Float.lt 0 (← TsModel.sq (Float.ofInt x))) :
        JsM Bool) =
      pure true

-- Wrong on purpose: the body never mentions b, so commutativity fails at
-- the first point with a ≠ b — a two-binder witness.
@[js_norm, grind]
def TsModel.comm (a _b : JsNumber) : JsM JsNumber := do
  return a + a

#thales_prove "cs.ts" "comm" "commutes" :=
  ballIco 0 10 fun a =>
    ballIco 0 10 fun b =>
      TsModel.comm (Float.ofInt a) (Float.ofInt b) =
        TsModel.comm (Float.ofInt b) (Float.ofInt a)

-- Zero binders: falsity without a witness to extract stays a GaveUp — the
-- envelope's falsified shape requires a non-empty counterexample. Only
-- hand-written artifacts can reach this; Lemma requires a binder.
#thales_prove "cs.ts" "bump" "atZero" :=
  TsModel.bump 0 = pure 0

-- A witness the budget cannot afford is still the same GaveUp, never a
-- Timeout: falsity is established by the second sweep of the domain and the
-- search that would name x = 99 is a third. The budget is tuned to fit two
-- sweeps and not three — heartbeats count allocations, not seconds, so the
-- window is machine-independent, but a toolchain bump can shift it.
set_option thales.heartbeats 3400 in
#thales_prove "cs.ts" "bump" "belowHundred" :=
  ballIco 0 100 fun x =>
    ((do
          return Float.lt (← TsModel.bump (Float.ofInt x)) 100) :
        JsM Bool) =
      pure true
