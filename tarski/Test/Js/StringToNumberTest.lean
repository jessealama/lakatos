import Js

open Js.Number

/-! StringToNumber and the two global parsers against Node 26: every value
below was read off the same expression there.

The three differ in what they demand of the rest of the string —
`stringToNumber` the whole of it, `parseFloat` the longest prefix, `parseInt`
the longest run of digits — and in nothing else, so the cases below are
grouped by that difference rather than by the grammar. -/

/-! ## StringToNumber, 7.1.4.1.1 -/

#guard (stringToNumber "").toBits == 0
#guard (stringToNumber "  ").toBits == 0
#guard stringToNumber "  12e-1 " == 1.2
#guard stringToNumber "0x1F" == 31
#guard stringToNumber "0X1f" == 31
#guard stringToNumber "0b101" == 5
#guard stringToNumber "0o17" == 15
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "-0x10")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "+0x10")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "0x")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "0xG")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "00x0")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "0x10.01")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "0b")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "0b2")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "0o8")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "1_0")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "infinity")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber ".")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "1e")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "e1")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "1e+")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "-")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "+")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "1 2")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "12abc")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "+Infinityx")
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber "\u180e")
#guard stringToNumber "Infinity" == Js.floatInf
#guard stringToNumber "+Infinity" == Js.floatInf
#guard stringToNumber "-Infinity" == -Js.floatInf
#guard stringToNumber "1." == 1
#guard stringToNumber ".5" == 0.5
#guard stringToNumber "+.5e1" == 5
#guard stringToNumber "-.5" == (-0.5)
#guard stringToNumber "1e+2" == 100
#guard stringToNumber "1E-2" == 0.01
#guard stringToNumber "000.1e1" == 1
#guard stringToNumber "0.1" == 0.1
#guard (stringToNumber "-0").toBits == 0x8000000000000000
#guard (stringToNumber "-1e-400").toBits == 0x8000000000000000
#guard stringToNumber "1234567890.1234567890" == 1234567890.1234567
#guard stringToNumber "0.12345678901234567890" == 0.12345678901234568
#guard stringToNumber "1e400" == Js.floatInf
#guard stringToNumber "1e99999999999999999999" == Js.floatInf
#guard stringToNumber "0xffffffffffffffffffff" == 1.2089258196146292e24
#guard stringToNumber "1234567890123456789012345678901234567890" == 1.2345678901234568e39
#guard (stringToNumber "1e-400").toBits == 0
#guard (stringToNumber "0e99999999999999999999").toBits == 0
#guard stringToNumber "4.9e-324" == 5e-324
#guard (stringToNumber "2.4703282292062327e-324").toBits == 0
#guard stringToNumber "2.4703282292062328e-324" == 5e-324
#guard stringToNumber "9007199254740993" == 9007199254740992
#guard stringToNumber "9007199254740995" == 9007199254740996
#guard stringToNumber "1.7976931348623158e308" == 1.7976931348623157e308
#guard stringToNumber "1.7976931348623159e308" == Js.floatInf

-- The twenty-four code points `StrWhiteSpaceChar` accepts, in one string:
-- they trim to nothing, and they trim away from a digit.
def whiteSpace : String := String.ofList
  [Char.ofNat 0x09, Char.ofNat 0x0A, Char.ofNat 0x0B, Char.ofNat 0x0C, Char.ofNat 0x0D,
   Char.ofNat 0x20, Char.ofNat 0xA0, Char.ofNat 0x1680, Char.ofNat 0x2000, Char.ofNat 0x2001,
   Char.ofNat 0x2002, Char.ofNat 0x2003, Char.ofNat 0x2004, Char.ofNat 0x2005, Char.ofNat 0x2006,
   Char.ofNat 0x2007, Char.ofNat 0x2008, Char.ofNat 0x2009, Char.ofNat 0x200A, Char.ofNat 0x2028,
   Char.ofNat 0x2029, Char.ofNat 0x202F, Char.ofNat 0x205F, Char.ofNat 0x3000, Char.ofNat 0xFEFF]

#guard (stringToNumber whiteSpace).toBits == 0
#guard stringToNumber (whiteSpace ++ "7" ++ whiteSpace) == 7
-- U+180E is not one of them, so it is not skipped.
#guard Js.Number.FloatOps.tsIsNaN (stringToNumber (String.ofList [Char.ofNat 0x180E, '7']))

-- A `String` is a byte array, so decoding one costs the kernel far more
-- reductions than the arithmetic it feeds; the pins raise the budget, and the
-- ones that go through a non-decimal base are stated over bits, which is the
-- shape whose decision procedure reduces.
set_option maxRecDepth 100000

example : stringToNumber "" = 0.0 := by decide
example : (stringToNumber "0x1F").toBits = (31.0 : Float).toBits := by decide
example : stringToNumber ".5" = 0.5 := by decide
example : Js.Number.FloatOps.tsIsNaN (stringToNumber "1_0") = true := by decide

/-! ## `parseFloat`, 19.2.4: the longest prefix -/

#guard parseFloat "1e" == 1
#guard parseFloat "1e+" == 1
#guard parseFloat "12e" == 12
#guard parseFloat "1.5.3" == 1.5
#guard parseFloat ".5x" == 0.5
#guard parseFloat "-.5" == (-0.5)
#guard parseFloat "+.5" == 0.5
#guard parseFloat "1.e3" == 1000
#guard parseFloat "1e-1e" == 0.1
#guard parseFloat "1e+5x" == 100000
#guard (parseFloat "0x10").toBits == 0
#guard parseFloat "Infinityx" == Js.floatInf
#guard parseFloat "Infinity1" == Js.floatInf
#guard parseFloat "-Infinityx" == -Js.floatInf
#guard parseFloat "  -11string" == (-11)
#guard parseFloat "01e1string" == 10
#guard parseFloat "0.1e1x" == 1
#guard parseFloat " 1" == 1
#guard parseFloat "1 " == 1
#guard parseFloat "1e400x" == Js.floatInf
#guard (parseFloat "-0").toBits == 0x8000000000000000
#guard (parseFloat "-1e-400").toBits == 0x8000000000000000
#guard Js.Number.FloatOps.tsIsNaN (parseFloat "")
#guard Js.Number.FloatOps.tsIsNaN (parseFloat "-")
#guard Js.Number.FloatOps.tsIsNaN (parseFloat ".")
#guard Js.Number.FloatOps.tsIsNaN (parseFloat "e1")
#guard Js.Number.FloatOps.tsIsNaN (parseFloat "  .e5")
#guard Js.Number.FloatOps.tsIsNaN (parseFloat "- 1")
#guard Js.Number.FloatOps.tsIsNaN (parseFloat "\u180e1")

example : parseFloat "1e" = 1.0 := by decide
example : parseFloat "  -11string" = -11.0 := by decide

/-! ## `parseInt`, 19.2.5: the longest run of radix digits

The radix arrives already through ToInt32, so `2.9` reaches this as `2` and
`2 ** 32 + 2` reaches it as `2`. -/

#guard Js.Number.FloatOps.tsIsNaN (parseInt "" (10))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "42" (1))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "42" (37))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "0x" (16))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "-" (10))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "8" (8))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "\u0661" (10))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "\u180e1" (10))
#guard Js.Number.FloatOps.tsIsNaN (parseInt "10" (-2))
#guard parseInt "010" (0) == 10
#guard parseInt "012" (8) == 10
#guard parseInt "0x1F" (0) == 31
#guard parseInt "0x1F" (16) == 31
#guard parseInt "0X1f" (0) == 31
#guard (parseInt "0x1F" (10)).toBits == 0
#guard (parseInt "0b101" (0)).toBits == 0
#guard parseInt "1Z" (36) == 71
#guard parseInt "1Z" (0) == 1
#guard parseInt "10$1" (2) == 2
#guard parseInt "10$1" (10) == 10
#guard parseInt "10$1" (36) == 36
#guard parseInt "  42abc" (0) == 42
#guard parseInt "11" (2) == 3
#guard parseInt "z" (36) == 35
#guard parseInt "Z" (36) == 35
#guard parseInt "7" (8) == 7
#guard parseInt "-12" (36) == (-38)
#guard parseInt "+5" (0) == 5
#guard parseInt "1e3" (0) == 1
#guard parseInt "  -0x10" (0) == (-16)
#guard parseInt "10" (2) == 2
#guard parseInt "9007199254740993" (10) == 9007199254740992
#guard parseInt "123456789012345678901234567890" (10) == 1.2345678901234568e29
#guard parseInt "ffffffffffffffffffff" (16) == 1.2089258196146292e24
#guard (parseInt "-0" (10)).toBits == 0x8000000000000000

example : (parseInt "0x1F" 0).toBits = (31.0 : Float).toBits := by decide
example : parseInt "11" 2 = 3.0 := by decide
example : Js.Number.FloatOps.tsIsNaN (parseInt "" 10) = true := by decide
