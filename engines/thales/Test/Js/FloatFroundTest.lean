import Js

open Js Js.Number.FloatOps

/-! `Math.fround`, built from `Float.Model` so the kernel can reduce it:
narrow to binary32 with roundTiesToEven, then widen back. NaN, the zeros,
and the infinities pass through with their sign; a magnitude beyond
binary32's range overflows to an infinity; a magnitude below its normal
range lands on a binary32 subnormal or a signed zero. Every pin is
bit-level and checked on both evaluation paths. Large magnitudes are
spelled as bit patterns: the elaborator cannot evaluate a literal like
`1e40`. -/

-- 0.1 is not a binary32 value; it rounds to 0.10000000149011612.
example : (tsFround 0.1).toBits = 0x3FB99999A0000000 := by decide
#guard (tsFround 0.1).toBits == 0x3FB99999A0000000

-- 1.5 is exact in binary32 and comes back unchanged.
example : (tsFround 1.5).toBits = 0x3FF8000000000000 := by decide
#guard (tsFround 1.5).toBits == 0x3FF8000000000000

-- The zeros keep their sign.
example : (tsFround 0.0).toBits = 0 := by decide
#guard (tsFround 0.0).toBits == 0
example : (tsFround (-0.0)).toBits = 0x8000000000000000 := by decide
#guard (tsFround (-0.0)).toBits == 0x8000000000000000

-- NaN and the infinities pass through.
example : (tsFround floatNaN).toBits = 0x7FF8000000000000 := by decide
#guard (tsFround floatNaN).toBits == 0x7FF8000000000000
example : (tsFround floatInf).toBits = 0x7FF0000000000000 := by decide
#guard (tsFround floatInf).toBits == 0x7FF0000000000000
example : (tsFround (-floatInf)).toBits = 0xFFF0000000000000 := by decide
#guard (tsFround (-floatInf)).toBits == 0xFFF0000000000000

-- 1e40 (bits 0x483D6329F1C35CA5) is beyond binary32's range: an infinity
-- of the input's sign.
example : (tsFround (Float.ofBits 0x483D6329F1C35CA5)).toBits = 0x7FF0000000000000 := by decide
#guard (tsFround (Float.ofBits 0x483D6329F1C35CA5)).toBits == 0x7FF0000000000000
example : (tsFround (Float.ofBits 0xC83D6329F1C35CA5)).toBits = 0xFFF0000000000000 := by decide
#guard (tsFround (Float.ofBits 0xC83D6329F1C35CA5)).toBits == 0xFFF0000000000000

-- The binary32 maximum (bits 0x47EFFFFFE0000000) survives; the next
-- binary64 value that rounds past it (0x47EFFFFFF0000000) overflows.
example : (tsFround (Float.ofBits 0x47EFFFFFE0000000)).toBits = 0x47EFFFFFE0000000 := by decide
#guard (tsFround (Float.ofBits 0x47EFFFFFE0000000)).toBits == 0x47EFFFFFE0000000
example : (tsFround (Float.ofBits 0x47EFFFFFF0000000)).toBits = 0x7FF0000000000000 := by decide
#guard (tsFround (Float.ofBits 0x47EFFFFFF0000000)).toBits == 0x7FF0000000000000

-- 1e-45 lands on the smallest binary32 subnormal, 2^-149.
example : (tsFround 1e-45).toBits = 0x36A0000000000000 := by decide
#guard (tsFround 1e-45).toBits == 0x36A0000000000000

-- Below half the smallest subnormal: a zero of the input's sign.
example : (tsFround (-1e-50)).toBits = 0x8000000000000000 := by decide
#guard (tsFround (-1e-50)).toBits == 0x8000000000000000

-- The binary64 minimum subnormal (bits 1): the deepest shift the model
-- performs, 925 bits.
set_option maxRecDepth 4096 in
example : (tsFround (Float.ofBits 1)).toBits = 0 := by decide
#guard (tsFround (Float.ofBits 1)).toBits == 0

-- 2^24 + 1 needs 25 significand bits; ties-to-even sends it down to 2^24.
-- This is the value a naive implementation gets wrong.
example : (tsFround 16777217.0).toBits = 0x4170000000000000 := by decide
#guard (tsFround 16777217.0).toBits == 0x4170000000000000
-- 2^24 + 3 ties up to 2^24 + 4, since 2^24 + 2 has an odd last bit.
example : (tsFround 16777219.0).toBits = 0x4170000040000000 := by decide
#guard (tsFround 16777219.0).toBits == 0x4170000040000000

-- Compiled oracle: core's own conversion, opaque to the kernel but
-- trustworthy for values, agrees with the model on every pin and more.
#guard
  [0.1, 1.5, 0.0, -0.0, floatNaN, floatInf, -floatInf,
   Float.ofBits 0x483D6329F1C35CA5, Float.ofBits 0xC83D6329F1C35CA5,
   Float.ofBits 0x47EFFFFFE0000000, Float.ofBits 0x47EFFFFFF0000000,
   1e-45, -1e-50, Float.ofBits 1, 16777217.0, 16777219.0,
   2.5e-45, -7.0e-40, 123456.789, 3.0e38, -1.0e-38, 1.0e-39].all
    fun x => (tsFround x).toBits == (Float.toFloat32 x).toFloat.toBits
