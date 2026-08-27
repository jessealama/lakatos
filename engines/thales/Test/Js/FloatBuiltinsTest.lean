import Js

open Js

/-! The builtin member calls the emitter whitelists delegate to core:
`Math.abs` is `Float.abs`, `Number.isFinite` is `Float.isFinite`,
`Number.isNaN` is `Float.isNaN`. ECMA-262 abs clears the sign — `-0`
becomes `+0`, NaN stays NaN — and the two predicates partition the
doubles into finite, infinite, and NaN. Pin the special cases on both
evaluation paths, because a split between them would be unsound, not
merely wrong. -/

-- Math.abs clears the sign bit. The zero pin is bit-level: Float
-- equality cannot see a signed zero.
example : (Float.abs (-0.0)).toBits = 0 := by decide
#guard (Float.abs (-0.0)).toBits == 0

example : Float.abs (-3.5) = 3.5 := by decide
#guard decide (Float.abs (-3.5) = 3.5)

-- `=` on Float is SameValue, so one NaN pins them all.
example : Float.abs floatNaN = floatNaN := by decide
#guard decide (Float.abs floatNaN = floatNaN)

example : Float.abs (-floatInf) = floatInf := by decide
#guard decide (Float.abs (-floatInf) = floatInf)

-- Number.isFinite is false exactly on NaN and the infinities.
example : Float.isFinite floatNaN = false := by decide
#guard Float.isFinite floatNaN == false

example : Float.isFinite floatInf = false := by decide
#guard Float.isFinite floatInf == false

example : Float.isFinite (-floatInf) = false := by decide
#guard Float.isFinite (-floatInf) == false

example : Float.isFinite (-0.0) = true := by decide
#guard Float.isFinite (-0.0)

-- The largest finite double is still finite. Elaboration blows the
-- recursion limit unpacking a literal this size; the kernel does not.
example : Float.isFinite 1.7976931348623157e308 = true := by decide +kernel
#guard Float.isFinite 1.7976931348623157e308

-- Number.isNaN is true exactly on NaN.
example : Float.isNaN floatNaN = true := by decide
#guard Float.isNaN floatNaN

example : Float.isNaN floatInf = false := by decide
#guard Float.isNaN floatInf == false

example : Float.isNaN (-0.0) = false := by decide
#guard Float.isNaN (-0.0) == false
