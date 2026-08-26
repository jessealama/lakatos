import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

@[js_norm, grind]
def TsModel.idg (x : JsNumber) : JsM JsNumber := do
  return x

-- true on the guarded slice: id keeps the floor its guard grants
#thales_prove "guard-chain-plain.lean" "idg" "single" :=
  ballIco 0 10 fun x =>
    (pure (Float.le 1 (Float.ofInt x)) : JsM Bool) = pure true →
      ((do
            return Float.le 1 (← TsModel.idg (Float.ofInt x))) :
          JsM Bool) =
        pure true

-- a two-guard chain, right-nested in guard order
#thales_prove "guard-chain-plain.lean" "idg" "chain" :=
  ballIco 0 10 fun x =>
    (pure (Float.le 1 (Float.ofInt x)) : JsM Bool) = pure true →
      (pure (Float.le 2 (Float.ofInt x)) : JsM Bool) = pure true →
        ((do
              return Float.le 2 (← TsModel.idg (Float.ofInt x))) :
            JsM Bool) =
          pure true

-- a constant-false guard: any conclusion holds vacuously
#thales_prove "guard-chain-plain.lean" "idg" "vacuous" :=
  ballIco 0 10 fun x =>
    (pure (Float.lt 1 0) : JsM Bool) = pure true →
      ((do
            return Float.lt (← TsModel.idg (Float.ofInt x)) 0) :
          JsM Bool) =
        pure true

-- a guard under a number binder: nothing is bounded, so the composition
-- reaches the symbolic rungs, which close the identity case from the
-- guard hypothesis
#thales_prove "guard-chain-plain.lean" "idg" "numberBinder" :=
  ∀ (x : JsNumber), 0 < x → x < floatInf →
    (pure (Float.le 1 x) : JsM Bool) = pure true →
      ((do
            return Float.le 1 (← TsModel.idg x)) :
          JsM Bool) =
        pure true

-- false on the guarded slice, and the witness respects the guard: the
-- first counterexample is the first x satisfying x >= 5, never x = 0
#thales_prove "guard-chain-plain.lean" "idg" "witness" :=
  ballIco 0 10 fun x =>
    (pure (Float.le 5 (Float.ofInt x)) : JsM Bool) = pure true →
      ((do
            return Float.le (← TsModel.idg (Float.ofInt x)) 4) :
          JsM Bool) =
        pure true
