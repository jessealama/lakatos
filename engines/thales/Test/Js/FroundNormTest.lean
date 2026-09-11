import Js

open Js Js.Number Js.Number.FloatOps

/-! The fround order theory must close under plain `grind`, with no lemma
list: every example is a residual shape the ladder actually emits. -/

-- The issue's residual: narrowing keeps the sign.
example : ∀ (x : JsNumber), Float.le 0 x = true → Float.le 0 (tsFround x) = true := by
  intro x h; grind

example : ∀ (x : JsNumber), Float.le x 0 = true → Float.le (tsFround x) 0 = true := by
  intro x h; grind

-- A bound binary32 represents exactly is kept.
example : ∀ (x : JsNumber), Float.le x 100 = true → Float.le (tsFround x) 100 = true := by
  intro x h; grind

example : ∀ (x : JsNumber), Float.le (-100) x = true → Float.le (-100) (tsFround x) = true := by
  intro x h; grind

-- A two-sided range makes the result finite. There is no unconditional
-- propagation: a finite input beyond binary32's range overflows.
example : ∀ (x : JsNumber), Float.le x (Float.ofBits 0x47EFFFFFE0000000) = true →
    Float.le (Float.ofBits 0xC7EFFFFFE0000000) x = true →
    Float.isFinite (tsFround x) = true := by
  intro x h1 h2; grind

-- Two applications: plain monotonicity.
example : ∀ (x y : JsNumber), Float.le x y = true →
    Float.le (tsFround x) (tsFround y) = true := by
  intro x y h; grind

-- Composition with a clamp.
example : ∀ (x : JsNumber), Float.isFinite x = true →
    Float.le (tsFround (tsMin x 5)) 5 = true := by
  intro x h; grind

-- The Prop spelling a binder bound arrives in.
example : ∀ (x : JsNumber), (0 : Float) ≤ x → Float.le 0 (tsFround x) = true := by
  intro x h; grind
