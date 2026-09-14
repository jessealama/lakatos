import Js

open Js Js.Number.FloatOps

/-! `Number::exponentiate`, the meaning of `**` and of `Math.pow`.

The specification's special-case table is exact, so every row of it is
pinned here on both evaluation paths — a split between them would be
unsound, not merely wrong. What the specification leaves
implementation-approximated is the finite/finite case, and `tsPow`
approximates it by repeated squaring: the integral exponents below are
the cases where that is the exact answer, and the last section is the
case where it is not an answer at all.

Large magnitudes are pinned by bits, because a decimal literal that size
blows the elaborator's recursion limit on the way to `decide`; the kernel
reduces the same term without trouble, so those rows are `decide +kernel`.
-/

/-! ## The exponent's NaN and zeros, which outrank everything -/

-- An exponent of either zero is 1 whatever the base, NaN included.
example : tsPow floatNaN 0.0 = 1.0 := by decide
#guard decide (tsPow floatNaN 0.0 = 1.0)
example : tsPow 1.0 0.0 = 1.0 := by decide
#guard decide (tsPow 1.0 0.0 = 1.0)
example : tsPow 3.0 0.0 = 1.0 := by decide
#guard decide (tsPow 3.0 0.0 = 1.0)
example : tsPow floatInf (-0.0) = 1.0 := by decide
#guard decide (tsPow floatInf (-0.0) = 1.0)

-- A NaN exponent is NaN, and so is a NaN base under any other exponent.
example : tsPow 2.0 floatNaN = floatNaN := by decide
#guard decide (tsPow 2.0 floatNaN = floatNaN)
example : tsPow floatNaN 1.0 = floatNaN := by decide
#guard decide (tsPow floatNaN 1.0 = floatNaN)

/-! ## An infinite base: the exponent's sign, and its oddness -/

example : tsPow floatInf 1.0 = floatInf := by decide
#guard decide (tsPow floatInf 1.0 = floatInf)
example : (tsPow floatInf (-1.0)).toBits = 0 := by decide
#guard (tsPow floatInf (-1.0)).toBits == 0

-- `-∞` keeps its sign only under an odd integral exponent.
example : tsPow (-floatInf) 3.0 = -floatInf := by decide
#guard decide (tsPow (-floatInf) 3.0 = -floatInf)
example : tsPow (-floatInf) 2.0 = floatInf := by decide
#guard decide (tsPow (-floatInf) 2.0 = floatInf)
example : (tsPow (-floatInf) (-3.0)).toBits = 0x8000000000000000 := by decide
#guard (tsPow (-floatInf) (-3.0)).toBits == 0x8000000000000000
example : (tsPow (-floatInf) (-2.0)).toBits = 0 := by decide
#guard (tsPow (-floatInf) (-2.0)).toBits == 0

-- A fractional exponent is not odd, so the positive branch is taken.
example : tsPow (-floatInf) 2.5 = floatInf := by decide
#guard decide (tsPow (-floatInf) 2.5 = floatInf)

/-! ## A zero base: the mirror of the infinite one -/

example : (tsPow 0.0 3.0).toBits = 0 := by decide
#guard (tsPow 0.0 3.0).toBits == 0
example : tsPow 0.0 (-3.0) = floatInf := by decide
#guard decide (tsPow 0.0 (-3.0) = floatInf)
example : (tsPow (-0.0) 3.0).toBits = 0x8000000000000000 := by decide
#guard (tsPow (-0.0) 3.0).toBits == 0x8000000000000000
example : (tsPow (-0.0) 2.0).toBits = 0 := by decide
#guard (tsPow (-0.0) 2.0).toBits == 0
example : tsPow (-0.0) (-3.0) = -floatInf := by decide
#guard decide (tsPow (-0.0) (-3.0) = -floatInf)
example : tsPow (-0.0) (-2.0) = floatInf := by decide
#guard decide (tsPow (-0.0) (-2.0) = floatInf)

/-! ## An infinite exponent: `abs(base)` against 1, and 1 itself is NaN -/

example : tsPow 2.0 floatInf = floatInf := by decide
#guard decide (tsPow 2.0 floatInf = floatInf)
example : (tsPow 0.5 floatInf).toBits = 0 := by decide
#guard (tsPow 0.5 floatInf).toBits == 0
example : (tsPow 2.0 (-floatInf)).toBits = 0 := by decide
#guard (tsPow 2.0 (-floatInf)).toBits == 0
example : tsPow 0.5 (-floatInf) = floatInf := by decide
#guard decide (tsPow 0.5 (-floatInf) = floatInf)

-- `abs(base) = 1` is NaN from either side and under either infinity: the
-- one place where a limit that exists mathematically is still NaN here.
example : tsPow 1.0 floatInf = floatNaN := by decide
#guard decide (tsPow 1.0 floatInf = floatNaN)
example : tsPow 1.0 (-floatInf) = floatNaN := by decide
#guard decide (tsPow 1.0 (-floatInf) = floatNaN)
example : tsPow (-1.0) (-floatInf) = floatNaN := by decide
#guard decide (tsPow (-1.0) (-floatInf) = floatNaN)

-- A negative base goes by its magnitude, sign and all: `abs(-0.5) < 1`.
example : (tsPow (-0.5) floatInf).toBits = 0 := by decide
#guard (tsPow (-0.5) floatInf).toBits == 0
example : tsPow (-0.5) (-floatInf) = floatInf := by decide
#guard decide (tsPow (-0.5) (-floatInf) = floatInf)

/-! ## Finite against finite, integral: where squaring is exact -/

example : (tsPow 2.0 53.0).toBits = 0x4340000000000000 := by decide +kernel
#guard (tsPow 2.0 53.0).toBits == 0x4340000000000000

-- `2 ** -52` is `Number.EPSILON`, bit for bit: the issue's own identity.
-- The hex spelling is what `decide` can reach; `EPSILON`'s own decimal
-- literal costs more to elaborate than the claim is worth, so that half
-- of the identity is pinned by evaluation alone.
example : (tsPow 2.0 (-52.0)).toBits = 0x3CB0000000000000 := by decide +kernel
#guard (tsPow 2.0 (-52.0)).toBits == 0x3CB0000000000000
#guard (tsPow 2.0 (-52.0)).toBits == Number.EPSILON.toBits

example : tsPow (-2.0) 3.0 = -8.0 := by decide
#guard decide (tsPow (-2.0) 3.0 = -8.0)
example : tsPow (-2.0) 2.0 = 4.0 := by decide
#guard decide (tsPow (-2.0) 2.0 = 4.0)
example : tsPow 1.5 2.0 = 2.25 := by decide
#guard decide (tsPow 1.5 2.0 = 2.25)
-- A negative exponent divides into 1, and the division's model is what
-- makes the elaborator's `decide` too slow here where the kernel's is not.
example : tsPow 2.0 (-2.0) = 0.25 := by decide +kernel
#guard decide (tsPow 2.0 (-2.0) = 0.25)
example : tsPow 2.0 10.0 = 1024.0 := by decide
#guard decide (tsPow 2.0 10.0 = 1024.0)

-- `10 ** 22` is the largest power of ten binary64 holds exactly, and
-- every intermediate square on the way to it is exact too.
example : (tsPow 10.0 22.0).toBits = 0x4480F0CF064DD592 := by decide +kernel
#guard (tsPow 10.0 22.0).toBits == 0x4480F0CF064DD592

-- Overflow and underflow come out of the squaring itself.
example : tsPow 2.0 1024.0 = floatInf := by decide +kernel
#guard decide (tsPow 2.0 1024.0 = floatInf)
example : (tsPow 0.5 1000000.0).toBits = 0 := by decide +kernel
#guard (tsPow 0.5 1000000.0).toBits == 0

/-! ## The honest limit: a non-integral exponent

A negative base under a fractional exponent is NaN by the specification,
and that row is real. A positive one is NaN only because this library has
no transcendental model and core's `Float.pow` has none either: `tsPow
4.0 0.5` is 2 in JavaScript. GitHub #434 is the model that would fix it;
until then the `Math.pow` and `**` built-ins carry this limit through,
and `Test/Tarski/MathTest.lean` pins the same row at the evaluator. -/

example : tsPow (-8.0) 0.5 = floatNaN := by decide
#guard decide (tsPow (-8.0) 0.5 = floatNaN)

-- JavaScript answers 2. This is the placeholder, not the truth.
example : tsPow 4.0 0.5 = floatNaN := by decide
#guard decide (tsPow 4.0 0.5 = floatNaN)

/-! ## The pieces underneath -/

-- `isOddInteger` is false on every non-integral value, on every even
-- one, and on the non-finite ones.
#guard isOddInteger 3.0
#guard isOddInteger (-3.0)
#guard isOddInteger 2.0 == false
#guard isOddInteger 2.5 == false
#guard isOddInteger 0.0 == false
#guard isOddInteger floatInf == false
#guard isOddInteger floatNaN == false
example : isOddInteger 3.0 = true := by decide
example : isOddInteger 2.0 = false := by decide

-- `natOfIntegral` is a magnitude: the sign is dropped, and a value that
-- is not an integral finite one answers 0.
#guard natOfIntegral (5.0 : Float).toModel.unpack == 5
#guard natOfIntegral (-5.0 : Float).toModel.unpack == 5
#guard natOfIntegral (0.0 : Float).toModel.unpack == 0
#guard natOfIntegral floatInf.toModel.unpack == 0
#guard natOfIntegral floatNaN.toModel.unpack == 0
example : natOfIntegral (5.0 : Float).toModel.unpack = 5 := by decide

-- `powNat` at the exponents the recursion's two arms cover.
#guard powNat 2.0 0 == 1.0
#guard powNat 2.0 1 == 2.0
#guard powNat 2.0 2 == 4.0
#guard powNat 2.0 3 == 8.0
#guard powNat 3.0 5 == 243.0
example : powNat 2.0 3 = 8.0 := by decide
