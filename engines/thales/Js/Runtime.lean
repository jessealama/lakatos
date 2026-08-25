namespace Js

/-- Runtime errors a JS program can raise. The payload is the error's
kind — the constructor a `throw new RangeError(...)` names — and nothing
more: a thrown message is a string the model has no way to build and no
property has any use for. -/
inductive JsError where
  | error (kind : String)
deriving Repr, DecidableEq

/-- The semantic domain of modeled JS functions: one computable monad for
every body — exceptions now, state and fuel when those slices land.
Computability is the property to preserve: `decide` must be able to
evaluate models over bounded domains. -/
abbrev JsM (α : Type) := Except JsError α

def JsM.throw {α : Type} (e : JsError) : JsM α := .error e

deriving instance DecidableEq for Except

end Js
