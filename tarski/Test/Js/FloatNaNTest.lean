import Js.Number.Basic
import Js.Number.FloatOps

open Js

-- IEEE `==` cannot see NaN as itself; SameValue can. Every fact reduces
-- in the kernel, which is what lets `decide` grade NaN-valued properties.
#guard floatNaN.isNaN
example : Float.beq floatNaN floatNaN = false := by decide
example : Number.FloatOps.sameValue floatNaN floatNaN = true := by decide
example : Float.le floatNaN 0.0 = false := by decide
example : Float.beq (1.0 + floatNaN) (1.0 + floatNaN) = false := by decide
