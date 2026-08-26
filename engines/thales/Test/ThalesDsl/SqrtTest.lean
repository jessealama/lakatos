import Js
import ThalesDsl.Prove

open ThalesDsl Js Js.Number

/-! `Math.sqrt` is exactly specified — ECMA-262 returns 𝔽(√ℝ(n)),
correctly rounded — and IEEE-754 sqrt is that rounding, so core
`Float.sqrt` is the model with nothing wrapped around it. Pin the
spec's special cases and one rounded irrational on both evaluation
paths, because a split between them would be unsound, not merely
wrong.

The finite arm reaches `Nat.sqrt`, whose Newton iteration is
well-founded, so it is spelled `decide +kernel`: elaboration declines
to unfold such a definition, the kernel does not, and the ladder's
proofs are kernel certificates. -/

-- An exact case and a correctly-rounded one (bits are the host
-- engine's Math.sqrt(2)).
example : Float.sqrt 4.0 = 2.0 := by decide +kernel
#guard decide (Float.sqrt 4.0 = 2.0)

example : Float.sqrt 2.0 = Float.ofBits 0x3ff6a09e667f3bcd := by decide +kernel
#guard decide (Float.sqrt 2.0 = Float.ofBits 0x3ff6a09e667f3bcd)

-- A negative argument is NaN; `=` on Float is SameValue, so one NaN
-- pins them all. The special cases answer without computing a root, so
-- elaboration reduces them on its own.
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

-- The shape a bounded obligation hands the kernel, once `>=` has
-- flipped and the Int binder has crossed to Float.
example : Float.le 0 (Float.sqrt (Float.ofInt 3)) = true := by decide +kernel
