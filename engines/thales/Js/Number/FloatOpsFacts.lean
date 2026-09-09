import Js.Number.FloatOps
import Js.Number.FloatFacts

/-!
Theory about the binary64 operations `FloatOps` builds: the defining
inequalities of `Math.min`/`Math.max` and of the integral roundings, and
the strict-bound propagation that lets a member's result feed a branch
condition or another operation. Everything is proven from `FloatFacts`'s
key semantics and kernel-checked.

Spelling follows `FloatFacts`: the infinities are `1.0 / 0.0` and its
negation. `Js/Norm.lean` restates on `floatInf` with grind patterns.
-/

namespace Js.Number.FloatOpsFacts

open Float.Model Float.Model.UnpackedFloat
open Js.Number.FloatFacts Js.Number.FloatOps

/-! ## Two order facts `FloatFacts` lacks at the `Float` layer -/

/-- `≤` is reflexive away from NaN. -/
theorem float_le_refl_of_ne_nan {b : Float} (hb : b.toModel.unpack ≠ .notANumber) :
    Float.le b b = true := by
  rw [float_le_unpack]
  exact le_of_key (canonical_unpack _) (canonical_unpack _) hb hb (Int.le_refl _)

/-- A true strict comparison is a true weak one. -/
theorem float_le_of_lt {a b : Float} (h : Float.lt a b = true) : Float.le a b = true := by
  rw [float_lt_unpack] at h
  rw [float_le_unpack]
  exact le_of_key (canonical_unpack _) (canonical_unpack _) (lt_ne_nan_left h) (lt_ne_nan_right h)
    (Int.le_of_lt (key_of_lt (canonical_unpack _) (canonical_unpack _) h))

/-- Totality away from NaN, on the NaN-exclusion spelling rather than the
bound spelling `FloatFacts.float_le_of_not_lt` takes. -/
theorem float_le_of_not_lt_of_ne_nan {x y : Float}
    (hx : x.toModel.unpack ≠ .notANumber) (hy : y.toModel.unpack ≠ .notANumber)
    (h : Float.lt x y = false) : Float.le y x = true := by
  rw [float_lt_unpack] at h
  rw [float_le_unpack]
  apply le_of_key (canonical_unpack _) (canonical_unpack _) hy hx
  apply Int.not_lt.mp
  intro hk
  have := lt_of_key (canonical_unpack _) (canonical_unpack _) hx hy hk
  exact Bool.noConfusion (this.symm.trans h)

/-! ## `Math.min` and `Math.max`

Each model is a five-arm match: two NaN arms the hypotheses exclude, two
zero-ordering arms that compare by `rfl` once the unpackings are
substituted, and the ordinary `if a < b` arm. -/

/-- `min` is at most its left operand. -/
theorem tsMin_le_left {a b : Float} (ha : a.toModel.unpack ≠ .notANumber)
    (hb : b.toModel.unpack ≠ .notANumber) : Float.le (tsMin a b) a = true := by
  unfold tsMin
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · rename_i ha' _
    rw [float_le_unpack, ha']
    rfl
  · rename_i sgn _ ha' hb'
    rw [float_le_unpack, hb', ha']
    cases sgn <;> rfl
  · split
    · exact float_le_refl_of_ne_nan ha
    · exact float_le_of_not_lt_of_ne_nan ha hb (Bool.eq_false_iff.mpr ‹_›)

/-- `min` is at most its right operand. -/
theorem tsMin_le_right {a b : Float} (ha : a.toModel.unpack ≠ .notANumber)
    (hb : b.toModel.unpack ≠ .notANumber) : Float.le (tsMin a b) b = true := by
  unfold tsMin
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · rename_i ha' hb'
    rw [float_le_unpack, ha', hb']
    rename_i s; cases s <;> rfl
  · rename_i _ hb'
    rw [float_le_unpack, hb']
    rfl
  · split
    · exact float_le_of_lt ‹_›
    · exact float_le_refl_of_ne_nan hb

/-- `max` is at least its left operand. -/
theorem tsMax_ge_left {a b : Float} (ha : a.toModel.unpack ≠ .notANumber)
    (hb : b.toModel.unpack ≠ .notANumber) : Float.le a (tsMax a b) = true := by
  unfold tsMax
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · rename_i ha' _
    rw [float_le_unpack, ha']
    rfl
  · rename_i sgn _ ha' hb'
    rw [float_le_unpack, ha', hb']
    cases sgn <;> rfl
  · split
    · exact float_le_of_lt ‹_›
    · exact float_le_refl_of_ne_nan ha

/-- `max` is at least its right operand. -/
theorem tsMax_ge_right {a b : Float} (ha : a.toModel.unpack ≠ .notANumber)
    (hb : b.toModel.unpack ≠ .notANumber) : Float.le b (tsMax a b) = true := by
  unfold tsMax
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · rename_i sgn _ ha' hb'
    rw [float_le_unpack, hb', ha']
    cases sgn <;> rfl
  · rename_i _ hb'
    rw [float_le_unpack, hb']
    rfl
  · split
    · exact float_le_refl_of_ne_nan hb
    · exact float_le_of_not_lt_of_ne_nan ha hb (Bool.eq_false_iff.mpr ‹_›)

/-- A lower bound of both operands is a lower bound of `min`. A true `≤`
already excludes NaN on both sides, so there is no side condition. -/
theorem tsMin_glb {a b c : Float} (ha : Float.le c a = true) (hb : Float.le c b = true) :
    Float.le c (tsMin a b) = true := by
  unfold tsMin
  split
  · rw [float_le_unpack] at ha
    exact absurd ‹_› (le_ne_nan_right ha)
  · rw [float_le_unpack] at hb
    exact absurd ‹_› (le_ne_nan_right hb)
  · exact ha
  · exact hb
  · split
    · exact ha
    · exact hb

/-- An upper bound of both operands is an upper bound of `max`. -/
theorem tsMax_lub {a b c : Float} (ha : Float.le a c = true) (hb : Float.le b c = true) :
    Float.le (tsMax a b) c = true := by
  unfold tsMax
  split
  · rw [float_le_unpack] at ha
    exact absurd ‹_› (le_ne_nan_left ha)
  · rw [float_le_unpack] at hb
    exact absurd ‹_› (le_ne_nan_left hb)
  · exact ha
  · exact hb
  · split
    · exact hb
    · exact ha

/-! ## Strict bounds propagate through `min` and `max`

The result is one of the operands whenever neither is NaN, and a strict
infinity bound on an operand already excludes NaN on that operand. -/

theorem tsMin_lo {a b : Float} (haLo : (-(1.0 / 0.0) : Float) < a)
    (hbLo : (-(1.0 / 0.0) : Float) < b) : (-(1.0 / 0.0) : Float) < tsMin a b := by
  have ha : Float.lt (-(1.0 / 0.0)) a = true := haLo
  have hb : Float.lt (-(1.0 / 0.0)) b = true := hbLo
  rw [float_lt_unpack] at ha hb
  unfold tsMin
  split
  · exact absurd ‹_› (lt_ne_nan_right ha)
  · exact absurd ‹_› (lt_ne_nan_right hb)
  · exact haLo
  · exact hbLo
  · split
    · exact haLo
    · exact hbLo

theorem tsMin_hi {a b : Float} (haHi : a < (1.0 / 0.0 : Float))
    (hbHi : b < (1.0 / 0.0 : Float)) : tsMin a b < (1.0 / 0.0 : Float) := by
  have ha : Float.lt a (1.0 / 0.0) = true := haHi
  have hb : Float.lt b (1.0 / 0.0) = true := hbHi
  rw [float_lt_unpack] at ha hb
  unfold tsMin
  split
  · exact absurd ‹_› (lt_ne_nan_left ha)
  · exact absurd ‹_› (lt_ne_nan_left hb)
  · exact haHi
  · exact hbHi
  · split
    · exact haHi
    · exact hbHi

theorem tsMax_lo {a b : Float} (haLo : (-(1.0 / 0.0) : Float) < a)
    (hbLo : (-(1.0 / 0.0) : Float) < b) : (-(1.0 / 0.0) : Float) < tsMax a b := by
  have ha : Float.lt (-(1.0 / 0.0)) a = true := haLo
  have hb : Float.lt (-(1.0 / 0.0)) b = true := hbLo
  rw [float_lt_unpack] at ha hb
  unfold tsMax
  split
  · exact absurd ‹_› (lt_ne_nan_right ha)
  · exact absurd ‹_› (lt_ne_nan_right hb)
  · exact haLo
  · exact hbLo
  · split
    · exact hbLo
    · exact haLo

theorem tsMax_hi {a b : Float} (haHi : a < (1.0 / 0.0 : Float))
    (hbHi : b < (1.0 / 0.0 : Float)) : tsMax a b < (1.0 / 0.0 : Float) := by
  have ha : Float.lt a (1.0 / 0.0) = true := haHi
  have hb : Float.lt b (1.0 / 0.0) = true := hbHi
  rw [float_lt_unpack] at ha hb
  unfold tsMax
  split
  · exact absurd ‹_› (lt_ne_nan_left ha)
  · exact absurd ‹_› (lt_ne_nan_left hb)
  · exact haHi
  · exact hbHi
  · split
    · exact hbHi
    · exact haHi

end Js.Number.FloatOpsFacts
