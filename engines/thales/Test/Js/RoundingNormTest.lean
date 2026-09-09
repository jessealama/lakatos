import Js

open Js Js.Number Js.Number.FloatOps

/-! The rounding order theory must close under plain `grind`, with no
lemma list: every goal is a residual the ladder actually emits. -/

-- The issue's third residual.
example : ∀ (x : JsNumber), Float.isFinite x = true → (tsFloor x).le x = true := by
  intro x h; grind

example : ∀ (x : JsNumber), Float.isFinite x = true → Float.le x (tsCeil x) = true := by
  intro x h; grind

-- Trunc by sign: the equation lets floor's fact carry.
example : ∀ (x : JsNumber), Float.isFinite x = true → Float.le 0 x = true →
    (tsTrunc x).le x = true := by
  intro x h h0; grind

example : ∀ (x : JsNumber), Float.isFinite x = true → Float.le x 0 = true →
    Float.le x (tsTrunc x) = true := by
  intro x h h0; grind

-- A rounding feeding min: the propagation lemmas carry the bounds across.
example : ∀ (x : JsNumber), Float.isFinite x = true → (tsMin (tsFloor x) 5).le 5 = true := by
  intro x h; grind

-- Floor under a branch the ladder split: totality on the false arm.
example : ∀ (x : JsNumber), Float.isFinite x = true →
    Float.lt (tsFloor x) 0 = false → Float.le 0 (tsFloor x) = true := by
  intro x h hb; grind

-- Chaining through a monotone operation.
example : ∀ (x : JsNumber), Float.isFinite x = true → Float.le (tsFloor x * 2) (x * 2) = true := by
  intro x h; grind
