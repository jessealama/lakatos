import Tarski.Value
import Js.Number.FloatOps

/-! Provisional value formatting for the executable.

`formatNumber` is the placeholder Number-to-String algorithm, and it is
named here, in one place, with what it does and does not do. #388
replaces this one function with ECMA's `Number::toString`; nothing else
changes. -/

namespace Tarski

open Js

/-- Drop a decimal string's trailing zeros, and the point with them when
nothing is left after it. -/
def trimFraction (s : String) : String :=
  if s.contains '.' then
    let rest := s.toList.reverse.dropWhile (· == '0')
    String.ofList (if rest.head? == some '.' then rest.tail.reverse else rest.reverse)
  else s

/-- A non-negative, non-zero magnitude. -/
def formatMagnitude (x : Float) : String :=
  if x.isInf then "Infinity"
  else if Number.FloatOps.tsIsSafeInteger x then toString x.toUInt64
  else trimFraction x.toString

/-- A number, as `String(x)` would print it — the placeholder
Number-to-String algorithm this slice runs everywhere a number becomes a
string: `String(x)`, `+` with a string operand, ToPropertyKey, and the
binary's own output.

It is **correct** for every integer of magnitude below 2^53, for both
zeros (which print `0`, the sign of zero being observable only through
`Object.is` and division), and for `NaN`, `Infinity`, and `-Infinity`.

It is **not** ECMA's `Number::toString` for anything else. A non-integer
prints the six fraction digits the runtime's own formatter gives rather
than the shortest round-tripping decimal, so `1/3` prints `0.333333`
where JS prints `0.3333333333333333`. A magnitude at or above 1e21
prints in full rather than in exponent form, so `1e21` prints
`1000000000000000000000` where JS prints `1e+21`. A magnitude small
enough to round to zero at six digits prints `0`. `Test/Tarski/FormatTest.lean`
pins each of those as the honest limit, and #388 is where they stop being
true. -/
def formatNumber (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0.0 then "0"
  else if Float.lt x 0.0 then "-" ++ formatMagnitude (-x)
  else formatMagnitude x

/-- A value, as the binary prints it. Both the string and the object arm
are reachable: a script may `throw "x"` or `throw {}`, and `describeThrown`
falls back to this for a thrown value that is not an Error object. -/
def formatValue : Value → String
  | .prim (.num x) => formatNumber x
  | .prim (.bool b) => if b then "true" else "false"
  | .prim .undef => "undefined"
  | .prim .null => "null"
  | .prim (.str s) => s
  | .prim (.bigint i) => toString i ++ "n"
  | .obj _ => "[object Object]"

end Tarski
