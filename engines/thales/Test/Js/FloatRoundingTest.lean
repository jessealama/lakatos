import Js

open Js Js.Number.FloatOps

/-! The rounding members the emitter whitelists: `Math.trunc`,
`Math.floor`, `Math.ceil`, `Math.round`, and `Math.sign`, built from
`Float.Model` so the kernel can reduce them. Every pin is bit-level and
checked on both evaluation paths. ECMA-262 fixes the signed zeros: a
magnitude below one that rounds to zero keeps the input's sign, so
`Math.ceil(-0.5)` is `-0` and `Math.trunc(-0.3)` is `-0`. -/

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

/-! ## `Math.round`: to nearest, halves toward +∞

Not `Math.floor(x + 0.5)`: that sum rounds before the floor does, and
disagrees with the spec on a half-open family of inputs. The pins below
include the smallest of them, the double just under one half — adding
`0.5` carries it to `1.0`, so the naive model answers one where ECMA-262
answers `+0`. -/

-- The largest double below one half (bits 0x3FDFFFFFFFFFFFFF). Rounds to
-- zero; `Math.floor(x + 0.5)` would answer one.
def justUnderHalf : Float := Float.ofBits 0x3FDFFFFFFFFFFFFF
example : (tsRound justUnderHalf).toBits = 0 := by decide
#guard (tsRound justUnderHalf).toBits == 0

-- A half rounds up, toward +∞ on both signs: 2.5 to 3, -2.5 to -2.
example : (tsRound 0.5).toBits = 0x3FF0000000000000 := by decide
#guard (tsRound 0.5).toBits == 0x3FF0000000000000
example : (tsRound 2.5).toBits = 0x4008000000000000 := by decide
#guard (tsRound 2.5).toBits == 0x4008000000000000
example : (tsRound (-2.5)).toBits = 0xC000000000000000 := by decide
#guard (tsRound (-2.5)).toBits == 0xC000000000000000

-- Past the half the magnitude grows on both signs.
example : (tsRound (-2.6)).toBits = 0xC008000000000000 := by decide
#guard (tsRound (-2.6)).toBits == 0xC008000000000000
example : (tsRound (-0.6)).toBits = 0xBFF0000000000000 := by decide
#guard (tsRound (-0.6)).toBits == 0xBFF0000000000000

-- Below the half the zero keeps the input's sign — including at exactly
-- -0.5, which the toward-+∞ tie rule sends to `-0`, not `-1`.
example : (tsRound 0.3).toBits = 0 := by decide
#guard (tsRound 0.3).toBits == 0
example : (tsRound (-0.4)).toBits = 0x8000000000000000 := by decide
#guard (tsRound (-0.4)).toBits == 0x8000000000000000
example : (tsRound (-0.5)).toBits = 0x8000000000000000 := by decide
#guard (tsRound (-0.5)).toBits == 0x8000000000000000

-- Already integral, and above 2^52 where every double is: unchanged.
example : (tsRound 7).toBits = 0x401C000000000000 := by decide
#guard (tsRound 7).toBits == 0x401C000000000000
example : (tsRound 4503599627370497).toBits = 0x4330000000000001 := by decide
#guard (tsRound 4503599627370497).toBits == 0x4330000000000001
example : (tsRound (-4503599627370497)).toBits = 0xC330000000000001 := by decide
#guard (tsRound (-4503599627370497)).toBits == 0xC330000000000001

-- Zeros, NaN, and the infinities pass through.
example : (tsRound 0.0).toBits = 0 := by decide
#guard (tsRound 0.0).toBits == 0
example : (tsRound (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsRound (-0.0)).toBits == 0x8000000000000000
example : tsRound floatNaN = floatNaN := by decide
#guard decide (tsRound floatNaN = floatNaN)
example : tsRound floatInf = floatInf := by decide
#guard decide (tsRound floatInf = floatInf)
example : tsRound (-floatInf) = -floatInf := by decide
#guard decide (tsRound (-floatInf) = -floatInf)

/-! ## `Math.sign`: the unit of the input's sign

NaN and both zeros come back unchanged — so `Math.sign(-0)` is `-0`, not
`0` — and everything else is `±1`, the infinities and the subnormals
included. -/

example : (tsSign 3.5).toBits = 0x3FF0000000000000 := by decide
#guard (tsSign 3.5).toBits == 0x3FF0000000000000
example : (tsSign (-3.5)).toBits = 0xBFF0000000000000 := by decide
#guard (tsSign (-3.5)).toBits == 0xBFF0000000000000

-- The zeros keep their sign rather than collapsing to a unit.
example : (tsSign 0.0).toBits = 0 := by decide
#guard (tsSign 0.0).toBits == 0
example : (tsSign (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsSign (-0.0)).toBits == 0x8000000000000000

-- A subnormal is nonzero, so it reports a unit like any other finite.
example : (tsSign maxSubnormal).toBits = 0x3FF0000000000000 := by decide
#guard (tsSign maxSubnormal).toBits == 0x3FF0000000000000
example : (tsSign (-maxSubnormal)).toBits = 0xBFF0000000000000 := by decide
#guard (tsSign (-maxSubnormal)).toBits == 0xBFF0000000000000

example : tsSign floatNaN = floatNaN := by decide
#guard decide (tsSign floatNaN = floatNaN)
example : tsSign floatInf = 1.0 := by decide
#guard decide (tsSign floatInf = 1.0)
example : tsSign (-floatInf) = -1.0 := by decide
#guard decide (tsSign (-floatInf) = -1.0)
