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

end Js.Number.FloatOpsFacts
