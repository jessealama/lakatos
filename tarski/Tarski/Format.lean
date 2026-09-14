import Tarski.Value
import Js.Number.ToString

/-! `Value → String` for the executable: what the binary prints for a
completion value, for a `print` argument, and for a thrown value that is not
an `Error` object.

The number arm is ECMA's `Number::toString`, which lives in the library
(`Js/Number/ToString.lean`) so that a run and a `Theorem` mean the same
thing by it. Nothing here formats a number itself. -/

namespace Tarski

open Js

/-- A value, as the binary prints it. Every arm is reachable: a script
may `throw "x"`, `throw {}`, or `throw Symbol()`, and `describeThrown`
falls back to this for a thrown value that is not an Error object. The
symbol arm is SymbolDescriptiveString, which is what `String(sym)`
answers and the one place a symbol becomes text without a `TypeError`. -/
def formatValue : Value → String
  | .prim (.num x) => Number.toDecimalString x
  | .prim (.bool b) => if b then "true" else "false"
  | .prim .undef => "undefined"
  | .prim .null => "null"
  | .prim (.str s) => s
  | .prim (.bigint i) => toString i ++ "n"
  | .obj _ => "[object Object]"
  | .sym s => s.descriptiveString

end Tarski
