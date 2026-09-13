import Tarski.Format

/-! The provisional formatter.

What is pinned here is what the binary prints, not ECMA's
`Number::toString`: an integral magnitude inside the safe range is exact,
both zeros print `0`, and the non-finite values print their JS spellings.
A non-integral value still prints the runtime's six fraction digits —
`1/3` below is the honest statement of that limit, and #388 is where it
stops being true. -/

open Tarski

#guard formatNumber 8.0 == "8"
#guard formatNumber 0.0 == "0"
#guard formatNumber (-0.0) == "0"
#guard formatNumber 2.5 == "2.5"
#guard formatNumber (-3.25) == "-3.25"
#guard formatNumber 123456789.0 == "123456789"
#guard formatNumber (0.0 / 0.0) == "NaN"
#guard formatNumber (1.0 / 0.0) == "Infinity"
#guard formatNumber (-1.0 / 0.0) == "-Infinity"

-- Provisional, and deliberately recorded as such: JS prints
-- `0.3333333333333333`.
#guard formatNumber (1.0 / 3.0) == "0.333333"

#guard formatValue (.prim (.num 8.0)) == "8"
#guard formatValue (.prim (.bool true)) == "true"
#guard formatValue (.prim (.bool false)) == "false"
#guard formatValue (.prim .undef) == "undefined"
#guard formatValue (.prim .null) == "null"
