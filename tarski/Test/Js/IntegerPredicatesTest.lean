import Js

open Js Js.Number.FloatOps

/-! `Number.isInteger` and `Number.isSafeInteger`. ECMA-262 defines both
through `IsIntegralNumber`: not finite is not integral, so NaN and the
infinities are false, and everything else is integral exactly when it
equals its own truncation. The zeros are integral —
`Number.isInteger(-0)` is `true` — which is why the comparison is the
IEEE one, matching the spec's comparison of real numbers, rather than
SameValue. `isSafeInteger` adds the magnitude bound 2^53 - 1. -/

-- The bound is exactly representable, so the comparison is exact.
example : (9007199254740991.0 : Float).toBits = 0x433FFFFFFFFFFFFF := by decide
#guard (9007199254740991.0 : Float).toBits == 0x433FFFFFFFFFFFFF

-- Integers and fractions.
example : tsIsInteger 2.0 = true := by decide
#guard tsIsInteger 2.0
example : tsIsInteger 2.5 = false := by decide
#guard !tsIsInteger 2.5
example : tsIsInteger (-2.0) = true := by decide
#guard tsIsInteger (-2.0)
example : tsIsInteger (-2.5) = false := by decide
#guard !tsIsInteger (-2.5)

-- Both zeros are integral.
example : tsIsInteger 0.0 = true := by decide
#guard tsIsInteger 0.0
example : tsIsInteger (-0.0) = true := by decide
#guard tsIsInteger (-0.0)

-- Not finite is not integral.
example : tsIsInteger floatNaN = false := by decide
#guard !tsIsInteger floatNaN
example : tsIsInteger floatInf = false := by decide
#guard !tsIsInteger floatInf
example : tsIsInteger (-floatInf) = false := by decide
#guard !tsIsInteger (-floatInf)

-- A subnormal is finite and nonzero, so it is not integral.
def maxSubnormal : Float := Float.ofBits 0x000FFFFFFFFFFFFF
example : tsIsInteger maxSubnormal = false := by decide
#guard !tsIsInteger maxSubnormal

-- Integral beyond the safe range: still an integer, not a safe one.
example : tsIsInteger 9007199254740992.0 = true := by decide
#guard tsIsInteger 9007199254740992.0
example : tsIsInteger 1e21 = true := by decide
#guard tsIsInteger 1e21

-- isSafeInteger agrees with isInteger inside the bound.
example : tsIsSafeInteger 2.0 = true := by decide
#guard tsIsSafeInteger 2.0
example : tsIsSafeInteger 2.5 = false := by decide
#guard !tsIsSafeInteger 2.5
example : tsIsSafeInteger 0.0 = true := by decide
#guard tsIsSafeInteger 0.0
example : tsIsSafeInteger (-0.0) = true := by decide
#guard tsIsSafeInteger (-0.0)

-- The bound is inclusive at 2^53 - 1 and excludes 2^53, both signs.
example : tsIsSafeInteger 9007199254740991.0 = true := by decide
#guard tsIsSafeInteger 9007199254740991.0
example : tsIsSafeInteger (-9007199254740991.0) = true := by decide
#guard tsIsSafeInteger (-9007199254740991.0)
example : tsIsSafeInteger 9007199254740992.0 = false := by decide
#guard !tsIsSafeInteger 9007199254740992.0
example : tsIsSafeInteger (-9007199254740992.0) = false := by decide
#guard !tsIsSafeInteger (-9007199254740992.0)
example : tsIsSafeInteger 1e21 = false := by decide
#guard !tsIsSafeInteger 1e21

-- Not finite is not safe either.
example : tsIsSafeInteger floatNaN = false := by decide
#guard !tsIsSafeInteger floatNaN
example : tsIsSafeInteger floatInf = false := by decide
#guard !tsIsSafeInteger floatInf
example : tsIsSafeInteger (-floatInf) = false := by decide
#guard !tsIsSafeInteger (-floatInf)
