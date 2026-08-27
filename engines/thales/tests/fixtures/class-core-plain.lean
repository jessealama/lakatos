-- Hand-written pin of the class-core artifact shapes: the structure, the
-- single-assignment constructor (both let and let-mut forms), a getter,
-- an instance-taking method, and obligations whose atoms build an
-- instance with new and call a method on it.
import ThalesDsl

open Js ThalesDsl

set_option autoImplicit false

structure TsModel.Box where
  «#v» : JsNumber

@[js_norm, grind]
def TsModel.Box.construct (v : JsNumber) : JsM TsModel.Box := do
  let «this.#v» : JsNumber := v
  return TsModel.Box.mk «this.#v»

@[js_norm, grind]
def TsModel.Box.v (self : TsModel.Box) : JsM JsNumber := do
  return TsModel.Box.«#v» self

#thales_prove "class-core-plain.ts" "Box#v" "roundTrip" :=
  ∀ (x : JsNumber),
    ((do return (← TsModel.Box.v (← TsModel.Box.construct x))) : JsM JsNumber) = pure x

@[js_norm, grind]
def TsModel.Box.double (self : TsModel.Box) : JsM JsNumber := do
  return TsModel.Box.«#v» self * 2

#thales_prove "class-core-plain.ts" "Box#double" "doubled" :=
  ∀ (x : JsNumber),
    ((do return (← TsModel.Box.double (← TsModel.Box.construct x))) : JsM JsNumber) =
      ((pure (x * 2) : JsM JsNumber))

structure TsModel.Gate where
  «#lo» : JsNumber

@[js_norm, grind]
def TsModel.Gate.construct (a : JsNumber) : JsM TsModel.Gate := do
  let mut «this.#lo» : JsNumber := 0
  if Float.lt a 0 then
    throw (JsError.error "RangeError")
  else
    «this.#lo» := a
  return TsModel.Gate.mk «this.#lo»

@[js_norm, grind]
def TsModel.Gate.lo (self : TsModel.Gate) : JsM JsNumber := do
  return TsModel.Gate.«#lo» self

#thales_prove "class-core-plain.ts" "Gate#lo" "keepsValue" :=
  ∀ (a : JsNumber),
    ((pure (Float.le 0 a) : JsM Bool) = pure true) →
      ((do return (← TsModel.Gate.lo (← TsModel.Gate.construct a))) : JsM JsNumber) = pure a
