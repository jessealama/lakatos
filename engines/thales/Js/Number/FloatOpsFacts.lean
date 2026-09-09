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

/-! ## The integral roundings

`roundIntegral`'s finite arm is `normalize (s.apply M) 0 s` with `M` the
shifted mantissa `q = m >>> k` or its successor. The rounding directions
reduce to three facts about that shift. -/

theorem shift_mul_le (m k : Nat) : (m >>> k) * 2 ^ k ≤ m := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_mul_le_self m (2 ^ k)

theorem lt_succ_shift_mul (m k : Nat) : m < (m >>> k + 1) * 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow, Nat.succ_mul]
  have h1 := Nat.div_add_mod m (2 ^ k)
  have h2 := Nat.mod_lt m (Nat.two_pow_pos k)
  rw [Nat.mul_comm] at h1
  omega

theorem exact_shift (m k : Nat) (h : m % 2 ^ k = 0) : (m >>> k) * 2 ^ k = m := by
  rw [Nat.shiftRight_eq_div_pow]
  have h1 := Nat.div_add_mod m (2 ^ k)
  rw [Nat.mul_comm] at h1
  omega

/-- What the floor arm rounds to, scaled back to the input's grid: at most
the input. Positive inputs never bump; negative ones bump exactly when the
dropped bits were nonzero. The `bump` match is spelled as `roundIntegral`
spells it, so the statement is what `dsimp` leaves in a goal. -/
theorem floor_int_le (s : Sign) (m k : Nat) :
    s.apply (if (match RoundDir.towardNegInf, s with
        | .towardZero, _ => false
        | .towardNegInf, .negative => (m % 2 ^ k != 0)
        | .towardNegInf, .positive => false
        | .towardPosInf, .positive => (m % 2 ^ k != 0)
        | .towardPosInf, .negative => false
        | .nearestHalfUp, .positive => decide (2 ^ (k - 1) ≤ m % 2 ^ k)
        | .nearestHalfUp, .negative => decide (2 ^ (k - 1) < m % 2 ^ k))
      then ((m >>> k : Nat) : Int) + 1 else ((m >>> k : Nat) : Int)) * (2 ^ k : Int)
      ≤ s.apply m := by
  cases s with
  | positive =>
    simp only [Sign.apply, Bool.false_eq_true, ite_false]
    exact_mod_cast shift_mul_le m k
  | negative =>
    simp only [Sign.apply]
    rw [Int.neg_mul]
    apply Int.neg_le_neg
    split
    · exact_mod_cast Nat.le_of_lt (lt_succ_shift_mul m k)
    · rename_i heq
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
      exact_mod_cast Nat.le_of_eq (exact_shift m k heq).symm

/-- The ceil arm: at least the input. The mirror of `floor_int_le`. -/
theorem ceil_int_ge (s : Sign) (m k : Nat) :
    s.apply m ≤
    s.apply (if (match RoundDir.towardPosInf, s with
        | .towardZero, _ => false
        | .towardNegInf, .negative => (m % 2 ^ k != 0)
        | .towardNegInf, .positive => false
        | .towardPosInf, .positive => (m % 2 ^ k != 0)
        | .towardPosInf, .negative => false
        | .nearestHalfUp, .positive => decide (2 ^ (k - 1) ≤ m % 2 ^ k)
        | .nearestHalfUp, .negative => decide (2 ^ (k - 1) < m % 2 ^ k))
      then ((m >>> k : Nat) : Int) + 1 else ((m >>> k : Nat) : Int)) * (2 ^ k : Int) := by
  cases s with
  | positive =>
    simp only [Sign.apply]
    split
    · exact_mod_cast Nat.le_of_lt (lt_succ_shift_mul m k)
    · rename_i heq
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
      exact_mod_cast Nat.le_of_eq (exact_shift m k heq).symm
  | negative =>
    simp only [Sign.apply, Bool.false_eq_true, ite_false]
    rw [Int.neg_mul]
    apply Int.neg_le_neg
    exact_mod_cast shift_mul_le m k

/-- The finite floor arm's key is at most the input's. The input is
rewritten as its own normalization so `key_normalize_mono_value` compares
the two, and the exponent split `1074 = k + (e + 1074)` reduces that to
`floor_int_le`. -/
theorem key_floor_finite_le {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hc : Canonical (.finite s m e h)) :
    key (roundIntegral .binary64 .towardNegInf (.finite s m e h)) ≤ key (.finite s m e h) := by
  obtain ⟨_, helo, _, _⟩ := canonical_finite_bounds hc
  dsimp only [roundIntegral]
  split
  · exact Int.le_refl _
  · rename_i he
    rw [← normalize_canonical_self hc]
    apply key_normalize_mono_value _ _ _ (by omega) helo
    have hk : (-e).toNat + (e + 1074).toNat = ((0 : Int) + 1074).toNat := by omega
    rw [← hk, int_pow_split, ← Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_right (floor_int_le s m (-e).toNat)
      (Int.le_of_lt (intPow_pos _))

/-- The finite ceil arm's key is at least the input's. -/
theorem key_ceil_finite_ge {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hc : Canonical (.finite s m e h)) :
    key (.finite s m e h) ≤ key (roundIntegral .binary64 .towardPosInf (.finite s m e h)) := by
  obtain ⟨_, helo, _, _⟩ := canonical_finite_bounds hc
  dsimp only [roundIntegral]
  split
  · exact Int.le_refl _
  · rename_i he
    rw [← normalize_canonical_self hc]
    apply key_normalize_mono_value _ _ _ helo (by omega)
    have hk : (-e).toNat + (e + 1074).toNat = ((0 : Int) + 1074).toNat := by omega
    rw [← hk, int_pow_split, ← Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_right (ceil_int_ge s m (-e).toNat)
      (Int.le_of_lt (intPow_pos _))

end Js.Number.FloatOpsFacts
