import Js
import ThalesDsl.Prove

open ThalesDsl Js Js.Number

/-! `≡` is SameValue, and an emitted equation is propositional equality on
`JsM Float`. That correspondence is an assumption the equation semantics
rests on, and `Float`'s equality is new enough to move, so pin it rather
than assert it. Each fact is pinned on both evaluation paths — `example`
for the kernel rung, `#guard` for the compiled one — because a split
between them would be unsound, not merely wrong. -/

/-! ## SameValue: `Object.is` agrees with `=` -/

-- Every NaN is one `Float` value, payload and sign included. Nothing can
-- observe a payload, which is exactly why `Object.is(NaN, NaN)` is true.
example : (0.0 / 0.0 : Float) = Float.ofBits 0x7ff8000000000001 := by decide
#guard decide ((0.0 / 0.0 : Float) = Float.ofBits 0x7ff8000000000001)

example : (0.0 / 0.0 : Float) = Float.ofBits 0xfff8000000000000 := by decide
#guard decide ((0.0 / 0.0 : Float) = Float.ofBits 0xfff8000000000000)

-- A NaN reached through arithmetic is the same value as a bare one.
example : (0.0 / 0.0 : Float) * 3.0 + 1.0 = 0.0 / 0.0 := by decide
#guard decide ((0.0 / 0.0 : Float) * 3.0 + 1.0 = 0.0 / 0.0)

-- Signed zeros stay distinct: `Object.is(-0, 0)` is false.
example : (-0.0 : Float) ≠ 0.0 := by decide
#guard decide ((-0.0 : Float) ≠ 0.0)

/-! ## `===` is IEEE, and departs from `≡` in exactly the two JS places -/

-- `Float.beq` is what `===` elaborates to: NaN loses, signed zeros tie.
example : ((0.0 / 0.0 : Float) == 0.0 / 0.0) = false := by decide
#guard !((0.0 / 0.0 : Float) == 0.0 / 0.0)

example : ((-0.0 : Float) == 0.0) = true := by decide
#guard ((-0.0 : Float) == 0.0)

/-! ## The shape an emitted equation builds -/

-- Equations compare `JsM Float`, so the correspondence has to survive the
-- monad, and a thrown side is equal to nothing.
#guard decide ((pure (0.0 / 0.0) : JsM Float) = pure (0.0 / 0.0))
#guard !decide ((pure (-0.0) : JsM Float) = pure 0.0)
#guard !decide ((pure 0.0 : JsM Float) = JsM.throw (.error "RangeError"))

/-! ## The Bool face the artifacts call -/

-- `Object.is` renders as `sameValue`, `=`'s decide: the corners above
-- must survive the wrapping, on both evaluation paths.
example : Number.FloatOps.sameValue (-0.0) 0.0 = false := by decide
#guard !(Number.FloatOps.sameValue (-0.0) 0.0)

example : Number.FloatOps.sameValue (0.0 / 0.0) (0.0 / 0.0) = true := by decide
#guard Number.FloatOps.sameValue (0.0 / 0.0) (0.0 / 0.0)

example : Number.FloatOps.sameValue 1.5 1.5 = true := by decide
#guard Number.FloatOps.sameValue 1.5 1.5
