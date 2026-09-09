import Js

open Js Js.Number Js.Number.FloatOps

/-! The Prop order on `Float` and the Bool comparison it unfolds to are one
value; grind must treat them as one atom, in both directions and for both
`≤` and `<`. Every goal closes under plain `grind`, no lemma list. -/

-- A bound-shaped hypothesis closes a property-shaped goal about the same pair.
example (a b : Float) (h : a ≤ b) : Float.le a b = true := by grind

example (a b : Float) (h : a < b) : Float.lt a b = true := by grind

-- And back: a property-shaped hypothesis reaches a bound-shaped goal.
example (a b : Float) (h : Float.le a b = true) : a ≤ b := by grind

example (a b : Float) (h : Float.lt a b = true) : a < b := by grind

-- A bounded binder proving its own bound restated as a property.
example : ∀ (x : JsNumber), -floatInf < x → x ≤ 10 → Float.le x 10 = true := by
  intro x hLo hHi; grind

-- The bridge feeds the existing Prop-keyed propagation: a Bool bound on a
-- finite value pins the value below `floatInf`.
example : ∀ (x : JsNumber), Float.le x 10 = true → x < floatInf := by
  intro x h; grind
