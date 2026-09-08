import Js

open Js Js.Number.FloatOps

/-! The rounding trio the emitter whitelists: `Math.trunc`, `Math.floor`,
`Math.ceil`, built from `Float.Model` so the kernel can reduce them. Every
pin is bit-level and checked on both evaluation paths. ECMA-262 fixes the
signed zeros: a magnitude below one that rounds to zero keeps the input's
sign, so `Math.ceil(-0.5)` is `-0` and `Math.trunc(-0.3)` is `-0`. -/

-- Positive and negative fractions: 2.5 and -2.5.
example : (tsTrunc 2.5).toBits = 0x4000000000000000 := by decide
#guard (tsTrunc 2.5).toBits == 0x4000000000000000
example : (tsFloor 2.5).toBits = 0x4000000000000000 := by decide
#guard (tsFloor 2.5).toBits == 0x4000000000000000
example : (tsCeil 2.5).toBits = 0x4008000000000000 := by decide
#guard (tsCeil 2.5).toBits == 0x4008000000000000

example : (tsTrunc (-2.5)).toBits = 0xC000000000000000 := by decide
#guard (tsTrunc (-2.5)).toBits == 0xC000000000000000
example : (tsFloor (-2.5)).toBits = 0xC008000000000000 := by decide
#guard (tsFloor (-2.5)).toBits == 0xC008000000000000
example : (tsCeil (-2.5)).toBits = 0xC000000000000000 := by decide
#guard (tsCeil (-2.5)).toBits == 0xC000000000000000

-- Magnitudes below one: the zero keeps the input's sign.
example : (tsTrunc 0.3).toBits = 0 := by decide
#guard (tsTrunc 0.3).toBits == 0
example : (tsFloor 0.3).toBits = 0 := by decide
#guard (tsFloor 0.3).toBits == 0
example : (tsCeil 0.3).toBits = 0x3FF0000000000000 := by decide
#guard (tsCeil 0.3).toBits == 0x3FF0000000000000

example : (tsTrunc (-0.3)).toBits = 0x8000000000000000 := by decide
#guard (tsTrunc (-0.3)).toBits == 0x8000000000000000
example : (tsFloor (-0.3)).toBits = 0xBFF0000000000000 := by decide
#guard (tsFloor (-0.3)).toBits == 0xBFF0000000000000
example : (tsCeil (-0.3)).toBits = 0x8000000000000000 := by decide
#guard (tsCeil (-0.3)).toBits == 0x8000000000000000

example : (tsCeil (-0.5)).toBits = 0x8000000000000000 := by decide
#guard (tsCeil (-0.5)).toBits == 0x8000000000000000

-- Already integral: unchanged, both signs.
example : (tsTrunc 7).toBits = 0x401C000000000000 := by decide
#guard (tsTrunc 7).toBits == 0x401C000000000000
example : (tsFloor (-7)).toBits = 0xC01C000000000000 := by decide
#guard (tsFloor (-7)).toBits == 0xC01C000000000000
example : (tsCeil (-7)).toBits = 0xC01C000000000000 := by decide
#guard (tsCeil (-7)).toBits == 0xC01C000000000000

-- Above 2^52 every double is integral: 4503599627370497 has no
-- fraction bits and all three leave it alone.
example : (tsTrunc 4503599627370497).toBits = 0x4330000000000001 := by decide
#guard (tsTrunc 4503599627370497).toBits == 0x4330000000000001
example : (tsFloor (-4503599627370497)).toBits = 0xC330000000000001 := by decide
#guard (tsFloor (-4503599627370497)).toBits == 0xC330000000000001
example : (tsCeil 4503599627370497).toBits = 0x4330000000000001 := by decide
#guard (tsCeil 4503599627370497).toBits == 0x4330000000000001

-- The largest subnormal (bits 0x000FFFFFFFFFFFFF): the deepest shift
-- the models perform.
def maxSubnormal : Float := Float.ofBits 0x000FFFFFFFFFFFFF
example : (tsTrunc maxSubnormal).toBits = 0 := by decide
#guard (tsTrunc maxSubnormal).toBits == 0
set_option maxRecDepth 4096 in
example : (tsCeil maxSubnormal).toBits = 0x3FF0000000000000 := by decide
#guard (tsCeil maxSubnormal).toBits == 0x3FF0000000000000
set_option maxRecDepth 4096 in
example : (tsFloor (-maxSubnormal)).toBits = 0xBFF0000000000000 := by decide
#guard (tsFloor (-maxSubnormal)).toBits == 0xBFF0000000000000
example : (tsCeil (-maxSubnormal)).toBits = 0x8000000000000000 := by decide
#guard (tsCeil (-maxSubnormal)).toBits == 0x8000000000000000

-- Zeros, NaN, and the infinities pass through.
example : (tsTrunc 0.0).toBits = 0 := by decide
#guard (tsTrunc 0.0).toBits == 0
example : (tsFloor (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsFloor (-0.0)).toBits == 0x8000000000000000
example : (tsCeil (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsCeil (-0.0)).toBits == 0x8000000000000000
example : tsTrunc floatNaN = floatNaN := by decide
#guard decide (tsTrunc floatNaN = floatNaN)
example : tsFloor floatInf = floatInf := by decide
#guard decide (tsFloor floatInf = floatInf)
example : tsCeil (-floatInf) = -floatInf := by decide
#guard decide (tsCeil (-floatInf) = -floatInf)
