import Js

open Js.Number.Decimal

/-! The exact decimal view of a binary64: that core's decimal-to-binary
conversion is what a Lean literal means, that the exact rational view and the
decimal exponent are what they claim to be, and that the shortest
round-tripping digits are the ones ECMA-262 6.1.6.1.20 step 5 describes.

Every expected pair below was read off Node 26 for the same value. The kernel
pins are the ordinary magnitudes; the two extremes need the raised thresholds
`FloatConstantsTest` uses for the same reason, their powers of ten being ~1100
bits of shifting. -/

/-! ## `ofScientific` is what a literal means -/

example : ofScientific 1 (-1) = (0.1 : Float) := by decide
example : ofScientific 3 (-1) = (0.3 : Float) := by decide
example : ofScientific 1 (-7) = (1e-7 : Float) := by decide
example : ofScientific 15 (-1) = (1.5 : Float) := by decide
set_option maxRecDepth 8192 in
example : ofScientific 1 21 = (1e21 : Float) := by decide
set_option maxRecDepth 8192 in
example : ofScientific 123456789012345680000 0 = (123456789012345680000 : Float) := by decide
#guard ofScientific 1 (-1) == (0.1 : Float)
#guard ofScientific 3 (-1) == (0.3 : Float)
#guard ofScientific 1 (-7) == (1e-7 : Float)
#guard ofScientific 15 (-1) == (1.5 : Float)
#guard ofScientific 1 21 == (1e21 : Float)
#guard ofScientific 123456789012345680000 0 == (123456789012345680000 : Float)

set_option exponentiation.threshold 1100 in
set_option maxRecDepth 8192 in
example : ofScientific 5 (-324) = Js.Number.MIN_VALUE := by decide

set_option exponentiation.threshold 1100 in
set_option maxRecDepth 8192 in
example : ofScientific 17976931348623157 292 = Js.Number.MAX_VALUE := by decide

#guard ofScientific 5 (-324) == Js.Number.MIN_VALUE
#guard ofScientific 17976931348623157 292 == Js.Number.MAX_VALUE

-- The sign is the caller's, so an underflowing negative literal is `-0`.
example : (withSign .negative (ofScientific 0 0)).toBits = 0x8000000000000000 := by decide
#guard (withSign .negative (ofScientific 1 (-400))).toBits == 0x8000000000000000
#guard (withSign .positive (ofScientific 0 0)).toBits == 0

/-! ## The exact rational view

`toModel.unpack` is canonical, so the mantissa is the normalised 53-bit one
and the fraction is not in lowest terms: `1.5` is `3 · 2^51` over `2^52`. -/

example : ratio (1.5 : Float).toModel.unpack = some (6755399441055744, 4503599627370496) := by decide
example : ratio (0.1 : Float).toModel.unpack = some (7205759403792794, 72057594037927936) := by decide
example : ratio (9007199254740992.0 : Float).toModel.unpack = some (9007199254740992, 1) := by decide
example : ratio (0.0 : Float).toModel.unpack = none := by decide
example : ratio (Js.floatInf).toModel.unpack = none := by decide
example : ratio (Js.floatNaN).toModel.unpack = none := by decide
#guard ratio (1.5 : Float).toModel.unpack == some (6755399441055744, 4503599627370496)
#guard ratio (0.1 : Float).toModel.unpack == some (7205759403792794, 72057594037927936)
#guard ratio (9007199254740992.0 : Float).toModel.unpack == some (9007199254740992, 1)

/-! ## The decimal exponent

The `n` with `10^(n-1) ≤ x < 10^n` for the **exact** value of the float, which
is not always the `n` of its shortest form: the float written `1e-6` is just
below `10^-6`, so its decimal exponent is `-6` and `shortest`'s carry arm is
what lifts it to `-5`. -/

def decExp (x : Float) : Int :=
  match ratio x.toModel.unpack with
  | none => 0
  | some (num, den) => decimalExponent num den

example : decExp 1.0 = 1 := by decide
example : decExp 1e21 = 22 := by decide
example : decExp 0.1 = 0 := by decide
example : decExp 100.0 = 3 := by decide
#guard decExp 1.0 == 1
#guard decExp 9.999999999999999e22 == 23
#guard decExp 1e21 == 22
#guard decExp 999999999999999900000 == 21
#guard decExp 0.1 == 0
#guard decExp 1e-7 == -7
#guard decExp 0.000001 == -6
#guard decExp 5e-324 == -323
#guard decExp 1.7976931348623157e308 == 309

/-! ## Rounding a scaled magnitude, ties up -/

def roundAt (x : Float) (p : Int) : Nat :=
  match ratio x.toModel.unpack with
  | none => 0
  | some (num, den) => roundHalfUpScaled num den p

example : roundAt 2.5 0 = 3 := by decide
example : roundAt 0.5 0 = 1 := by decide
example : roundAt 1.005 2 = 100 := by decide
#guard roundAt 2.5 0 == 3
#guard roundAt 0.5 0 == 1
-- `1.005` is below one and five thousandths, so it rounds down, not up.
#guard roundAt 1.005 2 == 100
#guard roundAt 1000000000000000128 0 == 1000000000000000128

/-! ## The shortest round-tripping digits -/

example : shortest 0.1 = some (1, 0) := by decide
example : shortest 1.5 = some (15, 1) := by decide
example : shortest 100.0 = some (1, 3) := by decide

#guard shortest 0.1 == some (1, 0)
#guard shortest (0.1 + 0.2) == some (30000000000000004, 0)
#guard shortest 1e21 == some (1, 22)
#guard shortest 123456789012345680000 == some (12345678901234568, 21)
#guard shortest 5e-324 == some (5, -323)
#guard shortest 9007199254740992 == some (9007199254740992, 16)
#guard shortest 1.7976931348623157e308 == some (17976931348623157, 309)
-- The `q + 1 = 10^k` arm: these two are one float, and its shortest form is
-- a digit longer than the level that found it.
#guard shortest 9.999999999999999e22 == some (1, 24)
#guard shortest 1e23 == some (1, 24)
#guard shortest (1.0 / 3.0) == some (3333333333333333, 0)
#guard shortest 9223372036854775808 == some (9223372036854776, 19)
-- The unequal-gap boundary and the subnormal below it.
#guard shortest 2.2250738585072014e-308 == some (22250738585072014, -307)
#guard shortest 1.1125369292536007e-308 == some (11125369292536007, -307)
#guard shortest 8.98846567431158e307 == some (898846567431158, 308)
#guard shortest 4.35 == some (435, 1)
#guard shortest 100.0 == some (1, 3)
#guard shortest 1000000000000000128 == some (10000000000000001, 19)
#guard shortest 12345678901234567890 == some (12345678901234567, 20)
#guard shortest Js.floatNaN == none
#guard shortest Js.floatInf == none
#guard shortest 0.0 == none
#guard shortest (-0.0) == none

set_option exponentiation.threshold 1100 in
set_option maxRecDepth 16384 in
example : shortest 5e-324 = some (5, -323) := by decide

/-! ## Digits of a natural -/

example : natToStringBase 16 255 = "ff" := by decide
example : natToStringBase 36 35 = "z" := by decide
example : natToStringBase 2 0 = "0" := by decide
example : decimalDigits 0 = "0" := by decide
example : digitCount 0 = 1 := by decide
example : digitCount 1000 = 4 := by decide
#guard natToStringBase 16 255 == "ff"
#guard natToStringBase 36 35 == "z"
#guard decimalDigits 1000000000000000128 == "1000000000000000128"
#guard digitCount 1000000000000000128 == 19
