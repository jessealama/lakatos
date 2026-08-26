import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

-- Pure-arithmetic model: function add(a: number, b: number): number { return a + b; }
@[js_norm, grind]
def TsModel.add (a b : JsNumber) : JsM JsNumber := do
  return a + b

-- Commutativity over a bounded domain: decidable, so decide yields Theorem.
#thales_prove "arith.ts" "add" "commutes" :=
  ballIco 0 10 fun a =>
    ballIco 0 10 fun b =>
      TsModel.add (Float.ofInt a) (Float.ofInt b) =
        TsModel.add (Float.ofInt b) (Float.ofInt a)

-- Boolean islands, one per comparison operator, over a range with negative
-- endpoints.
#thales_prove "arith.ts" "add" "growsStrictly" :=
  ballIco (-5) 5 fun a =>
    ((do
          return Float.lt (Float.ofInt a) (← TsModel.add (Float.ofInt a) 1)) :
        JsM Bool) =
      pure true

#thales_prove "arith.ts" "add" "belowSuccessor" :=
  ballIco (-5) 5 fun a =>
    ((do
          return Float.lt (Float.ofInt a) (← TsModel.add (Float.ofInt a) 1)) :
        JsM Bool) =
      pure true

#thales_prove "arith.ts" "add" "zeroBelow" :=
  ballIco (-5) 5 fun a =>
    ((do
          return Float.le (← TsModel.add (Float.ofInt a) 0) (Float.ofInt a)) :
        JsM Bool) =
      pure true

#thales_prove "arith.ts" "add" "zeroAbove" :=
  ballIco (-5) 5 fun a =>
    ((do
          return Float.le (Float.ofInt a) (← TsModel.add (Float.ofInt a) 0)) :
        JsM Bool) =
      pure true

#thales_prove "arith.ts" "add" "zeroEquates" :=
  ballIco (-5) 5 fun a =>
    ((do
          return Float.beq (← TsModel.add (Float.ofInt a) 0) (Float.ofInt a)) :
        JsM Bool) =
      pure true

#thales_prove "arith.ts" "add" "oneSeparates" :=
  ballIco (-5) 5 fun a =>
    ((do
          return !Float.beq (← TsModel.add (Float.ofInt a) 1) (Float.ofInt a)) :
        JsM Bool) =
      pure true

-- Binder values coerce into a Float body. Doubling is exact for every
-- representable integer, so this proves.
@[js_norm, grind]
def TsModel.dbl (x : JsNumber) : JsM JsNumber := do
  return x + x

#thales_prove "coerce.ts" "dbl" "doubles" :=
  ballIco 0 40 fun x =>
    TsModel.dbl (Float.ofInt x) = pure (Float.ofInt x * 2)

-- A domain far too large for the kernel tier to enumerate. The native tier
-- closes it in well under a second.
#thales_prove "coerce.ts" "dbl" "doublesWide" :=
  ballIco 0 20000 fun x =>
    TsModel.dbl (Float.ofInt x) = pure (Float.ofInt x * 2)

-- Nested ∀-properties (binders introduced by separate foralls).
#thales_prove "arith.ts" "add" "commutesNested" :=
  ballIco 0 5 fun a =>
    ballIco 0 5 fun b =>
      TsModel.add (Float.ofInt a) (Float.ofInt b) =
        TsModel.add (Float.ofInt b) (Float.ofInt a)
