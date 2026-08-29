import Js.Val

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
