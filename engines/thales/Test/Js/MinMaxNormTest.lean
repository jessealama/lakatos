import Js

open Js Js.Number Js.Number.FloatOps

/-! The `Math.min`/`Math.max` order theory must close under plain
`grind`: the grind rung hands the closer nothing beyond the patterns
registered in `Js.Norm`, so an explicit lemma list here would prove the
wrong thing. Every goal is a residual the ladder actually emits. -/

-- The issue's clamp, under its finiteness guard: the upper bound needs
-- `min ≤ right`, the lower needs the extremal fact through `max ≥ right`.
example : ∀ (x : JsNumber), Float.isFinite x = true →
    (tsMin (tsMax x 0) 5).le 5 = true := by
  intro x h; grind

example : ∀ (x : JsNumber), Float.isFinite x = true →
    Float.le 0 (tsMin (tsMax x 0) 5) = true := by
  intro x h; grind

-- A cap: `min ≤ left`.
example : ∀ (x : JsNumber), Float.isFinite x = true → (tsMin x 1).le x = true := by
  intro x h; grind

-- The clamp written max-outside: the extremal fact on `max`.
example : ∀ (x : JsNumber), Float.isFinite x = true →
    Float.le (tsMax (tsMin x 5) 0) 5 = true := by
  intro x h; grind

-- A bounded `number` binder spells the guard as two comparisons.
example : ∀ (x : JsNumber), -10 ≤ x → x ≤ 10 → (tsMin (tsMax x 0) 5).le 5 = true := by
  intro x h1 h2; grind

-- The result feeds a branch the ladder split: totality needs the
-- propagated bounds on `tsMin`.
example : ∀ (x : JsNumber), Float.isFinite x = true →
    Float.lt (tsMin x 1) 0 = false → Float.le 0 (tsMin x 1) = true := by
  intro x h hb; grind
