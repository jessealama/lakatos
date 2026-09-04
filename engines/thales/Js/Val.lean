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

@[js_norm, grind =] theorem JsVal.strictEq_num_null (x : Float) :
    JsVal.strictEq (.num x) .null = false := rfl

@[js_norm, grind =] theorem JsVal.sameValue_num_null (x : Float) :
    JsVal.sameValue (.num x) .null = false := rfl

@[js_norm, grind =] theorem JsVal.sameValue_null_null :
    JsVal.sameValue .null .null = true := rfl

@[js_norm, grind =] theorem JsVal.sameValue_num_undef (x : Float) :
    JsVal.sameValue (.num x) .undef = false := rfl

@[js_norm, grind =] theorem JsVal.sameValue_bool_num (b : Bool) (y : Float) :
    JsVal.sameValue (.bool b) (.num y) = false := rfl

@[js_norm, grind =] theorem JsVal.sameValue_num_bool (x : Float) (b : Bool) :
    JsVal.sameValue (.num x) (.bool b) = false := rfl

@[js_norm, grind =] theorem JsVal.sameValue_bool_bool (a b : Bool) :
    JsVal.sameValue (.bool a) (.bool b) = (a == b) := rfl

-- `deriving DecidableEq` routes `==` through `decide`, which no equation
-- of the norm set opens: the emitted tag test compares `typeof v` against
-- a literal, so the hit needs reflexivity and each miss its own ground
-- rewrite.
@[js_norm] theorem TypeofResult.beq_self (r : TypeofResult) :
    (r == r) = true := beq_self_eq_true r

@[js_norm, grind =] theorem TypeofResult.string_beq_number :
    (TypeofResult.string == TypeofResult.number) = false := rfl

/-- Project a value that may be absent — the domain for an optional
instance, which `JsVal` has no tag for. `none` throws the projection's
reserved error, exactly as `JsVal.toNumber` does on a wrong tag, so a
caller that has tested for presence never reaches the throw. -/
@[js_norm, grind]
def optionGet {α : Type} : Option α → JsM α
  | some v => pure v
  | none => JsM.throw (.error "type-projection")

-- `Option.isNone`/`isSome` on a literal constructor: the ground rewrites
-- a presence test reduces through.
@[js_norm, grind =] theorem isNone_some' {α : Type} (a : α) :
    (some a).isNone = false := rfl

@[js_norm, grind =] theorem isNone_none' {α : Type} :
    (none : Option α).isNone = true := rfl

@[js_norm, grind =] theorem isSome_some' {α : Type} (a : α) :
    (some a).isSome = true := rfl

@[js_norm, grind =] theorem isSome_none' {α : Type} :
    (none : Option α).isSome = false := rfl

end Js
