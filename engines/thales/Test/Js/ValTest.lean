import Js.Val

open Js

-- typeof is total on the six tags; null reports "object", the JS wart.
#guard decide (JsVal.typeof (.num 1.5) = TypeofResult.number)
#guard decide (JsVal.typeof (.str "a") = TypeofResult.string)
#guard decide (JsVal.typeof (.bigint 3) = TypeofResult.bigint)
#guard decide (JsVal.typeof (.bool true) = TypeofResult.boolean)
#guard decide (JsVal.typeof .undef = TypeofResult.undefined)
#guard decide (JsVal.typeof .null = TypeofResult.object)
