import Js.Runtime

open Js

-- JsM is computable and comparable: pure arithmetic runs to a value.
#guard decide ((pure 5 : JsM Int) = .ok 5)
#guard decide ((pure (2 + 3) : JsM Int) = (pure 5 : JsM Int))
#guard decide ((JsM.throw (.error "boom") : JsM Int) ≠ .ok 0)
