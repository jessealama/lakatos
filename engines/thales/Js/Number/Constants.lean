import Init.Data.Float.Model.Float
import Js.NormAttr
import Js.Number.Basic
import Js.Binders

/-!
The Number values ECMA-262 fixes as own properties of `Math` and
`Number`, under their source spellings so an artifact reads as the
program did. Each is one determinate double.

`MAX_VALUE` and `MIN_VALUE` are spelled by their bits: their decimal
spellings elaborate through `5^324`, which the kernel will not reduce
under the default thresholds, and a constant the decide rung cannot
evaluate would be useless in exactly the bounded claims that name it.
The three non-finite spellings are the atoms under another name, tagged
`js_norm` so the `floatInf`-keyed lemmas still fire once unfolded.
-/

namespace Js.Number

def EPSILON : Float := 2.220446049250313e-16
def MAX_SAFE_INTEGER : Float := 9007199254740991.0
def MIN_SAFE_INTEGER : Float := -9007199254740991.0
def MAX_VALUE : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF
def MIN_VALUE : Float := Float.ofBits 0x0000000000000001
@[js_norm] def POSITIVE_INFINITY : Float := floatInf
@[js_norm] def NEGATIVE_INFINITY : Float := -floatInf
@[js_norm] def NaN : Float := floatNaN

end Js.Number

namespace Js.Math

def E : Float := 2.718281828459045
def LN10 : Float := 2.302585092994046
def LN2 : Float := 0.6931471805599453
def LOG10E : Float := 0.4342944819032518
def LOG2E : Float := 1.4426950408889634
def PI : Float := 3.141592653589793
def SQRT1_2 : Float := 0.7071067811865476
def SQRT2 : Float := 1.4142135623730951

end Js.Math
