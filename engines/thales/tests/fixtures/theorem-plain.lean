import ThalesDsl

open Js ThalesDsl

-- Artifacts run under lean's defaults, not the lakefile's options, so the
-- header pins the one that matters: an unbound identifier must be an
-- error, never an auto-bound implicit.
set_option autoImplicit false

-- The plain-Lean emission shape: ordinary defs over the Js library, and a
-- #thales_prove whose payload is an ordinary Prop. The ballIco spine is
-- recovered syntactically, which is what puts the decide rung in reach.
def add (a b : JsNumber) : JsM JsNumber := do
  return a + b

def double (x : JsNumber) : JsM JsNumber := do
  return x * 2

#thales_prove "plain.ts" "add" "commutes" :=
  ballIco 0 10 fun a => ballIco 0 10 fun b =>
    add (Float.ofInt a) (Float.ofInt b) = add (Float.ofInt b) (Float.ofInt a)

-- A false property on a bounded domain still searches out its witness.
#thales_prove "plain.ts" "double" "fixed" :=
  ballIco 0 10 fun a => double (Float.ofInt a) = pure (Float.ofInt a)

-- The bare form: an obligation emitted with no structured payload.
#thales_prove "plain.ts" "dbl" "stub"
