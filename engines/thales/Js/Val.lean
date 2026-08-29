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

/-- JS `===` on the domain: no coercion, so cross-tag is `false`; on
`num` it is IEEE equality (NaN unequal to itself, the zeros equal). -/
@[js_norm, grind]
def JsVal.strictEq : JsVal → JsVal → Bool
  | .num x, .num y => x == y
  | .str a, .str b => a == b
  | .bigint a, .bigint b => a == b
  | .bool a, .bool b => a == b
  | .undef, .undef => true
  | .null, .null => true
  | _, _ => false

/-- SameValue on the domain — `Object.is`: like `strictEq` everywhere
except the `num` corners (NaN equals itself, the zeros differ). -/
@[js_norm, grind]
def JsVal.sameValue : JsVal → JsVal → Bool
  | .num x, .num y => Number.FloatOps.sameValue x y
  | .str a, .str b => a == b
  | .bigint a, .bigint b => a == b
  | .bool a, .bool b => a == b
  | .undef, .undef => true
  | .null, .null => true
  | _, _ => false

-- The catch-all arm compiles into an equation guarded by one hypothesis
-- per earlier arm, which `grind` cannot discharge; a cross-tag shape it
-- meets in practice therefore needs its own unconditional rewrite.
@[js_norm, grind =] theorem JsVal.strictEq_num_undef (x : Float) :
    JsVal.strictEq (.num x) .undef = false := rfl

end Js
