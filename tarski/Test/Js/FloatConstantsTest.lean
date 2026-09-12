import Js

open Js

/-! The Number values ECMA-262 fixes as own properties of `Math` and
`Number`, pinned to the bits a JavaScript engine holds for them on both
evaluation paths. The two extremes are also pinned to their decimal
spellings, so the bit definitions can never drift from what the source
means. -/

-- Number
example : Number.EPSILON.toBits = 0x3CB0000000000000 := by decide
#guard Number.EPSILON.toBits == 0x3CB0000000000000
example : Number.MAX_SAFE_INTEGER.toBits = 0x433FFFFFFFFFFFFF := by decide
#guard Number.MAX_SAFE_INTEGER.toBits == 0x433FFFFFFFFFFFFF
example : Number.MIN_SAFE_INTEGER.toBits = 0xC33FFFFFFFFFFFFF := by decide
#guard Number.MIN_SAFE_INTEGER.toBits == 0xC33FFFFFFFFFFFFF
example : Number.MAX_VALUE.toBits = 0x7FEFFFFFFFFFFFFF := by decide
#guard Number.MAX_VALUE.toBits == 0x7FEFFFFFFFFFFFFF
example : Number.MIN_VALUE.toBits = 0x0000000000000001 := by decide
#guard Number.MIN_VALUE.toBits == 0x0000000000000001
example : Number.POSITIVE_INFINITY.toBits = 0x7FF0000000000000 := by decide
#guard Number.POSITIVE_INFINITY.toBits == 0x7FF0000000000000
example : Number.NEGATIVE_INFINITY.toBits = 0xFFF0000000000000 := by decide
#guard Number.NEGATIVE_INFINITY.toBits == 0xFFF0000000000000
example : Number.NaN.toBits = 0x7FF8000000000000 := by decide
#guard Number.NaN.toBits == 0x7FF8000000000000

-- Math
example : Math.E.toBits = 0x4005BF0A8B145769 := by decide
#guard Math.E.toBits == 0x4005BF0A8B145769
example : Math.LN10.toBits = 0x40026BB1BBB55516 := by decide
#guard Math.LN10.toBits == 0x40026BB1BBB55516
example : Math.LN2.toBits = 0x3FE62E42FEFA39EF := by decide
#guard Math.LN2.toBits == 0x3FE62E42FEFA39EF
example : Math.LOG10E.toBits = 0x3FDBCB7B1526E50E := by decide
#guard Math.LOG10E.toBits == 0x3FDBCB7B1526E50E
example : Math.LOG2E.toBits = 0x3FF71547652B82FE := by decide
#guard Math.LOG2E.toBits == 0x3FF71547652B82FE
example : Math.PI.toBits = 0x400921FB54442D18 := by decide
#guard Math.PI.toBits == 0x400921FB54442D18
example : Math.SQRT1_2.toBits = 0x3FE6A09E667F3BCD := by decide
#guard Math.SQRT1_2.toBits == 0x3FE6A09E667F3BCD
example : Math.SQRT2.toBits = 0x3FF6A09E667F3BCD := by decide
#guard Math.SQRT2.toBits == 0x3FF6A09E667F3BCD

-- The three non-finite spellings are the atoms under another name.
example : Number.POSITIVE_INFINITY = floatInf := by decide
example : Number.NEGATIVE_INFINITY = -floatInf := by decide
example : Number.NaN = floatNaN := by decide

-- The extremes are spelled by their bits; their decimal spellings do not
-- reduce under the default thresholds, so the pin raises them.
set_option exponentiation.threshold 1100 in
set_option maxRecDepth 8192 in
example : Number.MIN_VALUE = (5e-324 : Float) := by decide

set_option exponentiation.threshold 1100 in
set_option maxRecDepth 8192 in
example : Number.MAX_VALUE = (1.7976931348623157e+308 : Float) := by decide

-- What the constants are for: EPSILON is the gap above one, the safe
-- bound is where the integer predicate turns.
example : Float.lt 1.0 (1.0 + Number.EPSILON) = true := by decide
example : Number.FloatOps.tsIsSafeInteger Number.MAX_SAFE_INTEGER = true := by decide
example : Number.FloatOps.tsIsSafeInteger (Number.MAX_SAFE_INTEGER + 1.0) = false := by decide
example : Float.isFinite Number.MAX_VALUE = true := by decide
example : Float.lt 0.0 Number.MIN_VALUE = true := by decide
