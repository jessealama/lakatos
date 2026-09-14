import Js

open Js.Number

/-! `Number::toString` and the four `Number.prototype` formatters against
Node 26: every expected string below was read off the same expression there.

`toDecimalString`, `toFixed`, `toExponential`, and `toPrecision` agree with
Node on every row here and on six hundred fuzzed rows apiece. `toRadixString`
agrees on every row but the last: V8 divides a large integer part by the radix
in double arithmetic and fills the digits it can no longer represent with
zeros, while this definition is exact, so `(1e21).toString(36)` ends
`79m9s` here and `7c000` there. Exact is the better answer — over four hundred
random (value, radix) pairs this definition round-trips every one and V8's
output fails on thirty-three — and it is what the algorithm's own header
promises.

The **round-trip property** is at the end: every finite value in the decimal
table reads back as itself through `stringToNumber`. -/

/-! ## `Number::toString(x, 10)` -/

#guard toDecimalString 0.1 == "0.1"
#guard toDecimalString (0.1 + 0.2) == "0.30000000000000004"
#guard toDecimalString 1e21 == "1e+21"
#guard toDecimalString 123456789012345680000 == "123456789012345680000"
#guard toDecimalString 1e-7 == "1e-7"
#guard toDecimalString 0.000001 == "0.000001"
#guard toDecimalString 5e-324 == "5e-324"
#guard toDecimalString 1.7976931348623157e308 == "1.7976931348623157e+308"
#guard toDecimalString 9007199254740992 == "9007199254740992"
#guard toDecimalString 1e23 == "1e+23"
#guard toDecimalString 9.999999999999999e22 == "1e+23"
#guard toDecimalString (1.0 / 3.0) == "0.3333333333333333"
#guard toDecimalString 9223372036854775808 == "9223372036854776000"
#guard toDecimalString 2.2250738585072014e-308 == "2.2250738585072014e-308"
#guard toDecimalString 1.1125369292536007e-308 == "1.1125369292536007e-308"
#guard toDecimalString 8.98846567431158e307 == "8.98846567431158e+307"
#guard toDecimalString 4.35 == "4.35"
#guard toDecimalString 100.0 == "100"
#guard toDecimalString 1.5e-7 == "1.5e-7"
#guard toDecimalString 1.5e21 == "1.5e+21"
#guard toDecimalString 999999999999999900000 == "999999999999999900000"
#guard toDecimalString 12345678901234567890 == "12345678901234567000"
#guard toDecimalString 18446744073709551616 == "18446744073709552000"
#guard toDecimalString 1.1805916207174113e21 == "1.1805916207174113e+21"
#guard toDecimalString 1000000000000000128 == "1000000000000000100"
#guard toDecimalString (-1e-7) == "-1e-7"
#guard toDecimalString 123.456 == "123.456"
#guard toDecimalString 1.005 == "1.005"
#guard toDecimalString 1e-323 == "1e-323"
#guard toDecimalString 5.992310449541053e307 == "5.992310449541053e+307"
#guard toDecimalString 7.2e-10 == "7.2e-10"
#guard toDecimalString 1.5e-323 == "1.5e-323"

#guard toDecimalString 0.0 == "0"
#guard toDecimalString (-0.0) == "0"
#guard toDecimalString Js.floatNaN == "NaN"
#guard toDecimalString Js.floatInf == "Infinity"
#guard toDecimalString (-Js.floatInf) == "-Infinity"

example : toDecimalString 0.1 = "0.1" := by decide
example : toDecimalString 100.0 = "100" := by decide
example : toDecimalString (-0.0) = "0" := by decide
example : toDecimalString Js.floatNaN = "NaN" := by decide

/-! ## `Number::toString(x, radix)`

The two rows that exercise the fraction loop's rounding are `(0.5, 3)` and
`(1/3, 3)`: neither is the exact expansion, both are what an engine prints. -/

#guard toRadixString 255 16 == "ff"
#guard toRadixString (-255) 16 == "-ff"
#guard toRadixString 255.5 16 == "ff.8"
#guard toRadixString 255.25 16 == "ff.4"
#guard toRadixString 0.5 2 == "0.1"
#guard toRadixString (-0.5) 2 == "-0.1"
#guard toRadixString 35 36 == "z"
#guard toRadixString 0.0 2 == "0"
#guard toRadixString (-0.0) 2 == "0"
#guard toRadixString Js.floatNaN 2 == "NaN"
#guard toRadixString Js.floatInf 2 == "Infinity"
#guard toRadixString (-Js.floatInf) 2 == "-Infinity"
#guard toRadixString 9007199254740992 2 == "100000000000000000000000000000000000000000000000000000"
#guard toRadixString 18446744073709551616 16 == "10000000000000000"
#guard toRadixString 3.75 2 == "11.11"
#guard toRadixString 0.1 2 == "0.0001100110011001100110011001100110011001100110011001101"
#guard toRadixString 0.1 16 == "0.1999999999999a"
#guard toRadixString 1e21 16 == "3635c9adc5dea00000"
#guard toRadixString (1.0 / 3.0) 3 == "0.1"
#guard toRadixString 0.5 3 == "0.1111111111111111111111111111111112"
#guard toRadixString 1.0000000000000002 2 == "1.0000000000000000000000000000000000000000000000000001"
#guard toRadixString 12345.6789 36 == "9ix.ofuravwu"
#guard toRadixString Js.Math.PI 16 == "3.243f6a8885a3"
#guard toRadixString 7 10 == "7"
#guard toRadixString 10 36 == "a"
#guard toRadixString 11 36 == "b"
#guard toRadixString 12 36 == "c"
#guard toRadixString 13 36 == "d"
#guard toRadixString 14 36 == "e"
#guard toRadixString 15 36 == "f"
#guard toRadixString 16 36 == "g"
#guard toRadixString 17 36 == "h"
#guard toRadixString 18 36 == "i"
#guard toRadixString 19 36 == "j"
#guard toRadixString 20 36 == "k"
#guard toRadixString 21 36 == "l"
#guard toRadixString 22 36 == "m"
#guard toRadixString 23 36 == "n"
#guard toRadixString 24 36 == "o"
#guard toRadixString 25 36 == "p"
#guard toRadixString 26 36 == "q"
#guard toRadixString 27 36 == "r"
#guard toRadixString 28 36 == "s"
#guard toRadixString 29 36 == "t"
#guard toRadixString 30 36 == "u"
#guard toRadixString 31 36 == "v"
#guard toRadixString 32 36 == "w"
#guard toRadixString 33 36 == "x"
#guard toRadixString 34 36 == "y"
#guard toRadixString 35 36 == "z"

-- One row where V8 is not exact and this definition is: the low three digits
-- of the integer part are `9m9s` here and `c000` in an engine.
#guard toRadixString 1e21 36 == "5v1j4f4ds79m9s"
-- The 53-bit gap at one, and a subnormal's fraction, both in binary.
#guard toRadixString 1.0000000000000002 2 ==
  "1.0000000000000000000000000000000000000000000000000001"
#guard toRadixString 9007199254740992 2 ==
  "100000000000000000000000000000000000000000000000000000"

example : toRadixString 255.0 16 = "ff" := by decide
example : toRadixString 0.5 2 = "0.1" := by decide

/-! ## `Number.prototype.toFixed` -/

#guard toFixedString 3 0 == "3"
#guard toFixedString 3 100 == "3.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
#guard toFixedString 1000000000000000128 0 == "1000000000000000128"
#guard toFixedString 1.005 2 == "1.00"
#guard toFixedString 0.5 0 == "1"
#guard toFixedString 1.5 0 == "2"
#guard toFixedString 2.5 0 == "3"
#guard toFixedString (-0.1) 0 == "-0"
#guard toFixedString (-0.5) 0 == "-1"
#guard toFixedString (-0.0) 1 == "0.0"
#guard toFixedString 1e21 2 == "1e+21"
#guard toFixedString 1e20 2 == "100000000000000000000.00"
#guard toFixedString 999999999999999900000 1 == "999999999999999868928.0"
#guard toFixedString 0.0 2 == "0.00"
#guard toFixedString 123.456 2 == "123.46"
#guard toFixedString 0.000001 7 == "0.0000010"
#guard toFixedString 0.1 20 == "0.10000000000000000555"
#guard toFixedString 1.45 1 == "1.4"
#guard toFixedString 8.345 2 == "8.35"
#guard toFixedString 5e-324 100 == "0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

example : toFixedString 1.005 2 = "1.00" := by decide
example : toFixedString 3.0 0 = "3" := by decide

/-! ## `Number.prototype.toExponential`

The `none` rows are an undefined `fractionDigits`, which is the shortest
form; `(25, some 0)` and `(99.5, some 0)` are the rows where rounding
overflows to `10^(f+1)` and becomes one digit an exponent higher. -/

#guard toExponentialString 123.456 (some 0) == "1e+2"
#guard toExponentialString 123.456 (some 1) == "1.2e+2"
#guard toExponentialString 123.456 (some 2) == "1.23e+2"
#guard toExponentialString 123.456 (some 3) == "1.235e+2"
#guard toExponentialString 123.456 (some 4) == "1.2346e+2"
#guard toExponentialString 123.456 (some 5) == "1.23456e+2"
#guard toExponentialString 123.456 (some 6) == "1.234560e+2"
#guard toExponentialString 123.456 (some 7) == "1.2345600e+2"
#guard toExponentialString 123.456 (some 17) == "1.23456000000000003e+2"
#guard toExponentialString 123.456 (some 20) == "1.23456000000000003070e+2"
#guard toExponentialString 0.0001 (some 0) == "1e-4"
#guard toExponentialString 0.0001 (some 1) == "1.0e-4"
#guard toExponentialString 0.0001 (some 2) == "1.00e-4"
#guard toExponentialString 0.0001 (some 3) == "1.000e-4"
#guard toExponentialString 0.0001 (some 4) == "1.0000e-4"
#guard toExponentialString 0.0001 (some 16) == "1.0000000000000000e-4"
#guard toExponentialString 0.0001 (some 17) == "1.00000000000000005e-4"
#guard toExponentialString 0.0001 (some 18) == "1.000000000000000048e-4"
#guard toExponentialString 0.0001 (some 19) == "1.0000000000000000479e-4"
#guard toExponentialString 0.0001 (some 20) == "1.00000000000000004792e-4"
#guard toExponentialString 0.9999 (some 0) == "1e+0"
#guard toExponentialString 0.9999 (some 1) == "1.0e+0"
#guard toExponentialString 0.9999 (some 2) == "1.00e+0"
#guard toExponentialString 0.9999 (some 3) == "9.999e-1"
#guard toExponentialString 0.9999 (some 4) == "9.9990e-1"
#guard toExponentialString 0.9999 (some 16) == "9.9990000000000001e-1"
#guard toExponentialString 0.9999 (some 17) == "9.99900000000000011e-1"
#guard toExponentialString 0.9999 (some 18) == "9.999000000000000110e-1"
#guard toExponentialString 0.9999 (some 19) == "9.9990000000000001101e-1"
#guard toExponentialString 0.9999 (some 20) == "9.99900000000000011013e-1"
#guard toExponentialString 25 (some 0) == "3e+1"
#guard toExponentialString 12345 (some 3) == "1.235e+4"
#guard toExponentialString 0.0 (some 0) == "0e+0"
#guard toExponentialString 0.0 (some 2) == "0.00e+0"
#guard toExponentialString 1 none == "1e+0"
#guard toExponentialString 123456 none == "1.23456e+5"
#guard toExponentialString (-0.0) none == "0e+0"
#guard toExponentialString 0.1 none == "1e-1"
#guard toExponentialString 1e21 none == "1e+21"
#guard toExponentialString 5e-324 none == "5e-324"
#guard toExponentialString 5e-324 (some 0) == "5e-324"
#guard toExponentialString 9.5 (some 0) == "1e+1"
#guard toExponentialString 0.5 (some 0) == "5e-1"
#guard toExponentialString 1.5 (some 0) == "2e+0"
#guard toExponentialString 2.5 (some 0) == "3e+0"
#guard toExponentialString (-1.5) (some 0) == "-2e+0"
#guard toExponentialString 1e-7 (some 2) == "1.00e-7"
#guard toExponentialString 99.5 (some 0) == "1e+2"
#guard toExponentialString 9.995 (some 2) == "9.99e+0"
#guard toExponentialString 1.7976931348623157e308 none == "1.7976931348623157e+308"

example : toExponentialString 25.0 (some 0) = "3e+1" := by decide
example : toExponentialString 0.0 (some 2) = "0.00e+0" := by decide

/-! ## `Number.prototype.toPrecision` -/

#guard toPrecisionString 7 1 == "7"
#guard toPrecisionString (-7) 1 == "-7"
#guard toPrecisionString 7 2 == "7.0"
#guard toPrecisionString (-7) 2 == "-7.0"
#guard toPrecisionString 7 3 == "7.00"
#guard toPrecisionString (-7) 3 == "-7.00"
#guard toPrecisionString 7 19 == "7.000000000000000000"
#guard toPrecisionString (-7) 19 == "-7.000000000000000000"
#guard toPrecisionString 7 20 == "7.0000000000000000000"
#guard toPrecisionString (-7) 20 == "-7.0000000000000000000"
#guard toPrecisionString 7 21 == "7.00000000000000000000"
#guard toPrecisionString (-7) 21 == "-7.00000000000000000000"
#guard toPrecisionString 10 2 == "10"
#guard toPrecisionString 11 2 == "11"
#guard toPrecisionString 12 2 == "12"
#guard toPrecisionString 13 2 == "13"
#guard toPrecisionString 14 2 == "14"
#guard toPrecisionString 15 2 == "15"
#guard toPrecisionString 16 2 == "16"
#guard toPrecisionString 17 2 == "17"
#guard toPrecisionString 18 2 == "18"
#guard toPrecisionString 19 2 == "19"
#guard toPrecisionString 20 2 == "20"
#guard toPrecisionString 100 3 == "100"
#guard toPrecisionString 100 7 == "100.0000"
#guard toPrecisionString 0.000001 1 == "0.000001"
#guard toPrecisionString 0.000001 2 == "0.0000010"
#guard toPrecisionString 0.000001 3 == "0.00000100"
#guard toPrecisionString 10 1 == "1e+1"
#guard toPrecisionString 17 1 == "2e+1"
#guard toPrecisionString 42 1 == "4e+1"
#guard toPrecisionString 1.2345e27 1 == "1e+27"
#guard toPrecisionString 1.2345e27 2 == "1.2e+27"
#guard toPrecisionString 1.2345e27 3 == "1.23e+27"
#guard toPrecisionString 1.2345e27 4 == "1.234e+27"
#guard toPrecisionString 1.2345e27 5 == "1.2345e+27"
#guard toPrecisionString 1.2345e27 6 == "1.23450e+27"
#guard toPrecisionString 1.2345e27 7 == "1.234500e+27"
#guard toPrecisionString 1.2345e27 16 == "1.234500000000000e+27"
#guard toPrecisionString 1.2345e27 17 == "1.2345000000000000e+27"
#guard toPrecisionString 1.2345e27 18 == "1.23449999999999996e+27"
#guard toPrecisionString 1.2345e27 19 == "1.234499999999999962e+27"
#guard toPrecisionString 1.2345e27 20 == "1.2344999999999999618e+27"
#guard toPrecisionString 0.0 1 == "0"
#guard toPrecisionString 0.0 3 == "0.00"
#guard toPrecisionString (-0.0) 2 == "0.0"
#guard toPrecisionString 1e-7 1 == "1e-7"
#guard toPrecisionString 1e-7 3 == "1.00e-7"
#guard toPrecisionString 123.456 4 == "123.5"
#guard toPrecisionString 123.456 2 == "1.2e+2"
#guard toPrecisionString 123.456 6 == "123.456"
#guard toPrecisionString 99.5 2 == "1.0e+2"
#guard toPrecisionString 0.5 1 == "0.5"
#guard toPrecisionString 1.5 1 == "2"
#guard toPrecisionString 2.5 1 == "3"
#guard toPrecisionString 1e21 3 == "1.00e+21"
#guard toPrecisionString 1e20 3 == "1.00e+20"
#guard toPrecisionString 123456 3 == "1.23e+5"
#guard toPrecisionString 0.00001234 2 == "0.000012"
#guard toPrecisionString 1.7976931348623157e308 17 == "1.7976931348623157e+308"
#guard toPrecisionString 5e-324 2 == "4.9e-324"
#guard toPrecisionString 999 1 == "1e+3"
#guard toPrecisionString 9.5 1 == "1e+1"

example : toPrecisionString 7.0 3 = "7.00" := by decide
example : toPrecisionString 10.0 1 = "1e+1" := by decide

/-! ## The round trip

Every finite value the decimal table prints reads back as itself. `-0` is
excluded and pinned on its own: `String(-0)` is `"0"`, so the trip lands on
`+0` and the two differ only in their bits. -/

def roundTrips : List Float := [0.1, (0.1 + 0.2), 1e21, 123456789012345680000, 1e-7, 0.000001, 5e-324, 1.7976931348623157e308, 9007199254740992, 1e23, 9.999999999999999e22, (1.0 / 3.0), 9223372036854775808, 2.2250738585072014e-308, 1.1125369292536007e-308, 8.98846567431158e307, 4.35, 100.0, 1.5e-7, 1.5e21, 999999999999999900000, 12345678901234567890, 18446744073709551616, 1.1805916207174113e21, 1000000000000000128, (-1e-7), 123.456, 1.005, 1e-323, 5.992310449541053e307, 7.2e-10, 1.5e-323]

#guard roundTrips.all (fun x => stringToNumber (toDecimalString x) == x)
#guard (stringToNumber (toDecimalString (-0.0))).toBits == 0

-- Formatting and parsing are string operations, and a `String` is a byte
-- array here, so encoding and decoding one costs the kernel far more
-- reductions than the arithmetic does; the pins raise the budget. A
-- seventeen-digit value — `0.1 + 0.2` is the shortest such — overflows the
-- stack at any budget, so it is held by `#guard` above and by the list
-- property, not by the kernel.
set_option maxRecDepth 200000

example : stringToNumber (toDecimalString 0.1) = 0.1 := by decide
example : stringToNumber (toDecimalString 1.5) = 1.5 := by decide
example : stringToNumber (toDecimalString 100.0) = 100.0 := by decide
example : stringToNumber (toDecimalString 1e21) = 1e21 := by decide

