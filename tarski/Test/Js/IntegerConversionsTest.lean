import Js

open Js.Number.FloatOps

/-! The two abstract operations that turn a Number into an integer, pinned on
both evaluation paths against Node 26 (`x | 0` for ToInt32, and the argument a
formatter's range check sees for ToIntegerOrInfinity).

`integerOrInfinity?` answers `none` for **either** infinity, so what these
pins say about `Infinity` and `-Infinity` is only that both are out of range;
the caller that needs to tell them apart has the Number itself. -/

/-! ## ToInt32, 7.1.6 -/

example : tsToInt32 0.0 = 0 := by decide
example : tsToInt32 (-0.0) = 0 := by decide
example : tsToInt32 Js.floatNaN = 0 := by decide
example : tsToInt32 Js.floatInf = 0 := by decide
example : tsToInt32 (-Js.floatInf) = 0 := by decide
example : tsToInt32 (-1.0) = -1 := by decide
example : tsToInt32 3.7 = 3 := by decide
example : tsToInt32 (-3.7) = -3 := by decide
#guard tsToInt32 0.0 == 0
#guard tsToInt32 (-0.0) == 0
#guard tsToInt32 Js.floatNaN == 0
#guard tsToInt32 Js.floatInf == 0
#guard tsToInt32 (-Js.floatInf) == 0
#guard tsToInt32 4294967298 == 2
#guard tsToInt32 2147483648 == -2147483648
#guard tsToInt32 (-1.0) == -1
#guard tsToInt32 3.7 == 3
#guard tsToInt32 (-3.7) == -3
#guard tsToInt32 1e20 == 1661992960
#guard tsToInt32 4294967295 == -1
#guard tsToInt32 (-4294967294) == 2
#guard tsToInt32 9007199254740992 == 0
#guard tsToInt32 (-2147483649) == 2147483647

/-! ## ToIntegerOrInfinity, 7.1.5 -/

example : integerOrInfinity? Js.floatNaN = some 0 := by decide
example : integerOrInfinity? 0.0 = some 0 := by decide
example : integerOrInfinity? (-0.0) = some 0 := by decide
example : integerOrInfinity? Js.floatInf = none := by decide
example : integerOrInfinity? (-Js.floatInf) = none := by decide
example : integerOrInfinity? 2.5 = some 2 := by decide
example : integerOrInfinity? (-2.5) = some (-2) := by decide
example : integerOrInfinity? 100.0 = some 100 := by decide
#guard integerOrInfinity? Js.floatNaN == some 0
#guard integerOrInfinity? 0.0 == some 0
#guard integerOrInfinity? (-0.0) == some 0
#guard integerOrInfinity? Js.floatInf == none
#guard integerOrInfinity? (-Js.floatInf) == none
#guard integerOrInfinity? 2.5 == some 2
#guard integerOrInfinity? (-2.5) == some (-2)
#guard integerOrInfinity? 100.0 == some 100
-- The magnitude is exact at every size: this is a hundred quintillion, not a
-- saturated `UInt64`.
#guard integerOrInfinity? 1e20 == some 100000000000000000000
