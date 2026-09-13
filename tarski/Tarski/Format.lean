import Tarski.Value
import Js.Number.FloatOps

/-! Provisional value formatting for the executable.

This is not ECMA's `Number::toString`: an integral magnitude inside the
safe range prints exactly, and everything else prints the six fraction
digits the runtime's own `Float.toString` gives, trimmed. `1/3` prints
`0.333333` where JS prints `0.3333333333333333`. #388 replaces this file
with the real algorithm — one file, one function, so that change touches
nothing else. -/

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

/-- A number, as `String(x)` would print it. Both zeros print `0`, as JS
does — the sign of zero is observable only through `Object.is` and
division. -/
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
