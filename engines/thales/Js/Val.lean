import Js.NormAttr
import Js.Runtime
import Js.Number.FloatOps

/-! The tagged value domain for positions typed beyond `number`: a union
slot holds one `JsVal`, injected by constructor at statically-typed
sites. Only values, tests, and projections live here — no coercions, no
string or bigint arithmetic. -/

namespace Js

/-- A JS value the model can hold beyond bare binary64. Payload types are
computable, so `decide` can evaluate anything built from them; `object`,
`function`, and `symbol` values have no representation here. -/
inductive JsVal where
  | num (x : Float)
  | str (s : String)
  | bigint (i : Int)
  | bool (b : Bool)
  | undef
  | null
deriving Repr

/-- What `typeof` can say: the full eight-result universe, closed, even
though three results are unreachable from `JsVal` — the enum models the
operator, not the domain. -/
inductive TypeofResult where
  | number
  | string
  | bigint
  | boolean
  | undefined
  | object
  | function
  | symbol
deriving DecidableEq, Repr

/-- `typeof`, total on the domain; `null` answers `object`, as JS does. -/
@[js_norm, grind]
def JsVal.typeof : JsVal → TypeofResult
  | .num _ => .number
  | .str _ => .string
  | .bigint _ => .bigint
  | .bool _ => .boolean
  | .undef => .undefined
  | .null => .object

/-- Project the `num` tag. The wrong-tag throw is the model refusing
coercion, not a claim JS throws here — hence a kind no `throw new X`
can spell. -/
@[js_norm, grind]
def JsVal.toNumber : JsVal → JsM Float
  | .num x => pure x
  | _ => JsM.throw (.error "type-projection")

end Js
