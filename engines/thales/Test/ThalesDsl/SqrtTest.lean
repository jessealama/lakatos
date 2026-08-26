import ThalesDsl.Prove

open ThalesDsl Js Js.Number

/-! `Math.sqrt` is exactly specified — ECMA-262 returns 𝔽(√ℝ(n)),
correctly rounded — and IEEE-754 sqrt is that rounding, so core
`Float.sqrt` is the model with nothing wrapped around it.

The two evaluation paths diverge here, and the split is a property of
Lean's model rather than of the semantics: `Float.sqrt`'s finite arm
calls `Nat.sqrt`, whose Newton iteration is well-founded rather than
structural, so the kernel cannot unfold it. Facts about finite
arguments are pinned on the compiled path alone; the special-case arms
answer without computing, so those are pinned on both. -/

-- An exact case and a correctly-rounded one (bits are the host
-- engine's Math.sqrt(2)). Compiled path only: see above.
#guard decide (Float.sqrt 4.0 = 2.0)
#guard decide (Float.sqrt 2.0 = Float.ofBits 0x3ff6a09e667f3bcd)

-- A negative argument is NaN; `=` on Float is SameValue, so one NaN
-- pins them all.
example : Float.sqrt (-1.0) = 0.0 / 0.0 := by decide
#guard decide (Float.sqrt (-1.0) = 0.0 / 0.0)

example : Float.sqrt (0.0 / 0.0) = 0.0 / 0.0 := by decide
#guard decide (Float.sqrt (0.0 / 0.0) = 0.0 / 0.0)

-- The zeros keep their signs, and +∞ is a fixed point.
example : Float.sqrt (-0.0) = -0.0 := by decide
#guard decide (Float.sqrt (-0.0) = -0.0)

example : Float.sqrt 0.0 = 0.0 := by decide
#guard decide (Float.sqrt 0.0 = 0.0)

example : Float.sqrt (1.0 / 0.0) = 1.0 / 0.0 := by decide
#guard decide (Float.sqrt (1.0 / 0.0) = 1.0 / 0.0)

-- What carries the finite arm instead of evaluation: non-negativity is
-- a theorem, so a bounded domain proves without the kernel computing a
-- single root.
example (x : Float) (hx : Float.le 0 x = true) :
    Float.le 0 (Float.sqrt x) = true :=
  FloatFacts.float_sqrt_nonneg hx
