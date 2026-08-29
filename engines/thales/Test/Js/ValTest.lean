import Js.Val
import Js.Number.Basic

open Js

-- typeof is total on the six tags; null reports "object", the JS wart.
#guard decide (JsVal.typeof (.num 1.5) = TypeofResult.number)
#guard decide (JsVal.typeof (.str "a") = TypeofResult.string)
#guard decide (JsVal.typeof (.bigint 3) = TypeofResult.bigint)
#guard decide (JsVal.typeof (.bool true) = TypeofResult.boolean)
#guard decide (JsVal.typeof .undef = TypeofResult.undefined)
#guard decide (JsVal.typeof .null = TypeofResult.object)

-- The projection: pure on the matching tag, one reserved throw otherwise.
-- "type-projection" is not a JS constructor name on purpose: JS coerces
-- here rather than throwing, so the throw is the model refusing coercion.
#guard decide ((JsVal.num 2.5).toNumber = pure 2.5)
#guard decide ((JsVal.str "x").toNumber = (JsM.throw (.error "type-projection") : JsM Float))
#guard decide ((JsVal.bigint 7).toNumber = (JsM.throw (.error "type-projection") : JsM Float))
#guard decide ((JsVal.bool false).toNumber = (JsM.throw (.error "type-projection") : JsM Float))
#guard decide (JsVal.undef.toNumber = (JsM.throw (.error "type-projection") : JsM Float))
#guard decide (JsVal.null.toNumber = (JsM.throw (.error "type-projection") : JsM Float))

-- The two JS equalities diverge only at the num corners: strictEq is
-- IEEE (NaN unequal, zeros conflated), sameValue is SameValue.
#guard JsVal.strictEq (.num 1.5) (.num 1.5)
#guard !JsVal.strictEq (.num floatNaN) (.num floatNaN)
#guard JsVal.strictEq (.num (-0.0)) (.num 0.0)
#guard JsVal.sameValue (.num floatNaN) (.num floatNaN)
#guard !JsVal.sameValue (.num (-0.0)) (.num 0.0)

-- Same-tag payload comparison on the other tags.
#guard JsVal.strictEq (.str "a") (.str "a")
#guard !JsVal.strictEq (.str "a") (.str "b")
#guard JsVal.strictEq (.bigint 3) (.bigint 3)
#guard !JsVal.strictEq (.bigint 3) (.bigint 4)
#guard JsVal.strictEq (.bool true) (.bool true)
#guard !JsVal.strictEq (.bool true) (.bool false)
#guard JsVal.strictEq .undef .undef
#guard JsVal.strictEq .null .null
#guard JsVal.sameValue (.str "a") (.str "a")
#guard JsVal.sameValue .undef .undef

-- Neither predicate coerces: cross-tag is false, undef/null included.
#guard !JsVal.strictEq (.num 0.0) .undef
#guard !JsVal.strictEq .undef .null
#guard !JsVal.strictEq (.num 1.0) (.str "1")
#guard !JsVal.sameValue (.num 0.0) .undef
#guard !JsVal.sameValue .undef .null
#guard !JsVal.sameValue (.bigint 1) (.num 1.0)

-- The norm set must evaluate the domain on constructor heads: this is
-- the discharge story union-typed models rely on, pinned symbolically
-- (with a variable payload, so kernel reduction can't do it alone).
example (x : Float) : (JsVal.num x).toNumber = pure x := by
  simp only [js_norm]
example (x : Float) : (JsVal.num x).typeof = TypeofResult.number := by
  simp only [js_norm]
example (s : String) : (JsVal.str s).toNumber =
    (JsM.throw (.error "type-projection") : JsM Float) := by
  simp only [js_norm]
example (x : Float) : JsVal.strictEq (.num x) .undef = false := by
  simp only [js_norm]
example (x : Float) : JsVal.sameValue .undef (.num x) = false := by
  simp only [js_norm]

-- grind opens the same doors on its own.
example (x : Float) : (JsVal.num x).toNumber = pure x := by grind
example (x : Float) : JsVal.strictEq (.num x) .undef = false := by grind
