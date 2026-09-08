import Js

open Js Js.Number.FloatOps

/-! `Math.min` and `Math.max`, built from `Float.Model` so the kernel can
reduce them. Every pin is bit-level and checked on both evaluation paths.
Two ECMA-262 clauses separate these from an ordinary comparison, and Lean's
order-derived generic `min`/`max` get both wrong: a NaN operand makes the
result NaN rather than being dropped, and the two zeros are ordered even
though they compare equal. -/

-- A NaN operand wins from either side, and comes back canonical.
example : (tsMin floatNaN 1.0).toBits = 0x7FF8000000000000 := by decide
#guard (tsMin floatNaN 1.0).toBits == 0x7FF8000000000000
example : (tsMin 1.0 floatNaN).toBits = 0x7FF8000000000000 := by decide
#guard (tsMin 1.0 floatNaN).toBits == 0x7FF8000000000000
example : (tsMax floatNaN 1.0).toBits = 0x7FF8000000000000 := by decide
#guard (tsMax floatNaN 1.0).toBits == 0x7FF8000000000000
example : (tsMax 1.0 floatNaN).toBits = 0x7FF8000000000000 := by decide
#guard (tsMax 1.0 floatNaN).toBits == 0x7FF8000000000000
example : (tsMin floatNaN floatNaN).toBits = 0x7FF8000000000000 := by decide
#guard (tsMin floatNaN floatNaN).toBits == 0x7FF8000000000000
example : (tsMax floatNaN floatNaN).toBits = 0x7FF8000000000000 := by decide
#guard (tsMax floatNaN floatNaN).toBits == 0x7FF8000000000000

-- The zeros compare equal, so the answer cannot be read off `<`: `min`
-- takes the negative one and `max` the positive one, from either order.
example : (tsMin 0.0 (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsMin 0.0 (-0.0)).toBits == 0x8000000000000000
example : (tsMin (-0.0) 0.0).toBits = 0x8000000000000000 := by decide
#guard (tsMin (-0.0) 0.0).toBits == 0x8000000000000000
example : (tsMax 0.0 (-0.0)).toBits = 0 := by decide
#guard (tsMax 0.0 (-0.0)).toBits == 0
example : (tsMax (-0.0) 0.0).toBits = 0 := by decide
#guard (tsMax (-0.0) 0.0).toBits == 0

-- Two like zeros keep their sign.
example : (tsMin 0.0 0.0).toBits = 0 := by decide
#guard (tsMin 0.0 0.0).toBits == 0
example : (tsMin (-0.0) (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsMin (-0.0) (-0.0)).toBits == 0x8000000000000000
example : (tsMax 0.0 0.0).toBits = 0 := by decide
#guard (tsMax 0.0 0.0).toBits == 0
example : (tsMax (-0.0) (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsMax (-0.0) (-0.0)).toBits == 0x8000000000000000

-- A zero against a nonzero is an ordinary comparison; the sign rule does
-- not reach it.
example : (tsMin (-0.0) 0.5).toBits = 0x8000000000000000 := by decide
#guard (tsMin (-0.0) 0.5).toBits == 0x8000000000000000
example : (tsMin 0.0 (-0.5)).toBits = 0xBFE0000000000000 := by decide
#guard (tsMin 0.0 (-0.5)).toBits == 0xBFE0000000000000
example : (tsMax (-0.0) (-0.5)).toBits = 0x8000000000000000 := by decide
#guard (tsMax (-0.0) (-0.5)).toBits == 0x8000000000000000
example : (tsMax 0.0 (-0.5)).toBits = 0 := by decide
#guard (tsMax 0.0 (-0.5)).toBits == 0

-- Ordinary comparisons, in both argument orders, and a repeated operand.
example : (tsMin 1.0 2.0).toBits = 0x3FF0000000000000 := by decide
#guard (tsMin 1.0 2.0).toBits == 0x3FF0000000000000
example : (tsMin 2.0 1.0).toBits = 0x3FF0000000000000 := by decide
#guard (tsMin 2.0 1.0).toBits == 0x3FF0000000000000
example : (tsMax 1.0 2.0).toBits = 0x4000000000000000 := by decide
#guard (tsMax 1.0 2.0).toBits == 0x4000000000000000
example : (tsMax 2.0 1.0).toBits = 0x4000000000000000 := by decide
#guard (tsMax 2.0 1.0).toBits == 0x4000000000000000
example : (tsMin (-2.5) 2.5).toBits = 0xC004000000000000 := by decide
#guard (tsMin (-2.5) 2.5).toBits == 0xC004000000000000
example : (tsMax (-2.5) 2.5).toBits = 0x4004000000000000 := by decide
#guard (tsMax (-2.5) 2.5).toBits == 0x4004000000000000
example : (tsMin 2.5 2.5).toBits = 0x4004000000000000 := by decide
#guard (tsMin 2.5 2.5).toBits == 0x4004000000000000
example : (tsMax 2.5 2.5).toBits = 0x4004000000000000 := by decide
#guard (tsMax 2.5 2.5).toBits == 0x4004000000000000

-- The infinities are the identities: they lose to every other value on
-- their own side and win on the other.
example : (tsMin floatInf 5.0).toBits = 0x4014000000000000 := by decide
#guard (tsMin floatInf 5.0).toBits == 0x4014000000000000
example : (tsMax floatInf 5.0).toBits = 0x7FF0000000000000 := by decide
#guard (tsMax floatInf 5.0).toBits == 0x7FF0000000000000
example : (tsMin (-floatInf) 5.0).toBits = 0xFFF0000000000000 := by decide
#guard (tsMin (-floatInf) 5.0).toBits == 0xFFF0000000000000
example : (tsMax (-floatInf) 5.0).toBits = 0x4014000000000000 := by decide
#guard (tsMax (-floatInf) 5.0).toBits == 0x4014000000000000
example : (tsMin floatInf floatInf).toBits = 0x7FF0000000000000 := by decide
#guard (tsMin floatInf floatInf).toBits == 0x7FF0000000000000
example : (tsMin floatInf (-floatInf)).toBits = 0xFFF0000000000000 := by decide
#guard (tsMin floatInf (-floatInf)).toBits == 0xFFF0000000000000

-- Subnormals, which the unpacked view reaches at its deepest shift.
def maxSubnormal : Float := Float.ofBits 0x000FFFFFFFFFFFFF
example : (tsMin maxSubnormal 1.0).toBits = 0x000FFFFFFFFFFFFF := by decide
#guard (tsMin maxSubnormal 1.0).toBits == 0x000FFFFFFFFFFFFF
example : (tsMax (-maxSubnormal) (-1.0)).toBits = 0x800FFFFFFFFFFFFF := by decide
#guard (tsMax (-maxSubnormal) (-1.0)).toBits == 0x800FFFFFFFFFFFFF
example : (tsMin 0.0 maxSubnormal).toBits = 0 := by decide
#guard (tsMin 0.0 maxSubnormal).toBits == 0
example : (tsMin (-0.0) maxSubnormal).toBits = 0x8000000000000000 := by decide
#guard (tsMin (-0.0) maxSubnormal).toBits == 0x8000000000000000
example : (tsMax maxSubnormal floatNaN).toBits = 0x7FF8000000000000 := by decide
#guard (tsMax maxSubnormal floatNaN).toBits == 0x7FF8000000000000
