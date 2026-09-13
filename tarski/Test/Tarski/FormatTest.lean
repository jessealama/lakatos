import Tarski.Format

/-! The provisional formatter.

What is pinned here is what the binary prints, not ECMA's
`Number::toString`: an integral magnitude inside the safe range is exact,
both zeros print `0`, and the non-finite values print their JS spellings.
The three cases at the end are the honest statement of the limits
`Tarski/Format.lean`'s doc comment names — no shortest round-trip, no
exponent form, nothing below six fraction digits — and #388 is where they
stop being true. -/

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

-- Provisional, and deliberately recorded as such. `Tarski/Format.lean`'s
-- doc comment is the one place that says what the placeholder does not
-- do; these are the cases it names.
--
-- JS prints `0.3333333333333333`.
#guard formatNumber (1.0 / 3.0) == "0.333333"

-- JS prints `1e+21`: there is no exponent form here.
#guard formatNumber 1e21 == "1000000000000000000000"

-- JS prints `1e-7`: a magnitude below the six fraction digits is lost.
#guard formatNumber 1e-7 == "0"

#guard formatValue (.prim (.num 8.0)) == "8"
#guard formatValue (.prim (.bool true)) == "true"
#guard formatValue (.prim (.bool false)) == "false"
#guard formatValue (.prim .undef) == "undefined"
#guard formatValue (.prim .null) == "null"
