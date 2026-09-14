import Tarski.Format

/-! What the binary prints for a value.

The number arm is the library's `Number::toString` (`Test/Js/NumberToStringTest.lean`
is where that algorithm is pinned against an engine), so the three cases
this file used to record as the placeholder's limits — no shortest
round-trip, no exponent form, nothing below six fraction digits — are now
right, and they are kept below as the pins that say so. -/

open Tarski

#guard formatValue (.prim (.num 8.0)) == "8"
#guard formatValue (.prim (.num 0.0)) == "0"
#guard formatValue (.prim (.num (-0.0))) == "0"
#guard formatValue (.prim (.num 2.5)) == "2.5"
#guard formatValue (.prim (.num (-3.25))) == "-3.25"
#guard formatValue (.prim (.num 123456789.0)) == "123456789"
#guard formatValue (.prim (.num (0.0 / 0.0))) == "NaN"
#guard formatValue (.prim (.num (1.0 / 0.0))) == "Infinity"
#guard formatValue (.prim (.num (-1.0 / 0.0))) == "-Infinity"

-- The three the placeholder used to get wrong.
#guard formatValue (.prim (.num (1.0 / 3.0))) == "0.3333333333333333"
#guard formatValue (.prim (.num 1e21)) == "1e+21"
#guard formatValue (.prim (.num 1e-7)) == "1e-7"

#guard formatValue (.prim (.bool true)) == "true"
#guard formatValue (.prim (.bool false)) == "false"
#guard formatValue (.prim .undef) == "undefined"
#guard formatValue (.prim .null) == "null"
#guard formatValue (.prim (.str "x")) == "x"
#guard formatValue (.obj 0) == "[object Object]"

-- A symbol prints as SymbolDescriptiveString, which is what `tarski run`
-- writes for a completion value and what `describeThrown` falls back to
-- for `throw Symbol()`.
#guard formatValue (.sym { id := 0, description := some "k" }) == "Symbol(k)"
#guard formatValue (.sym { id := 0, description := some "" }) == "Symbol()"
#guard formatValue (.sym { id := 0 }) == "Symbol()"
