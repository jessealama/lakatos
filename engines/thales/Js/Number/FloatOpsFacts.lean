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

/-! ## IEEE equality at the `Float` layer

`beq` is key equality away from NaN, so it is reflexive there, transitive,
and antisymmetry's conclusion: the currency the emitter's `===` uses. -/

theorem float_beq_refl_of_ne_nan {a : Float} (ha : a.toModel.unpack ≠ .notANumber) :
    Float.beq a a = true := by
  rw [float_beq_unpack]
  exact beq_of_key (canonical_unpack _) (canonical_unpack _) ha ha rfl

theorem float_beq_trans {a b c : Float} (h1 : Float.beq a b = true)
    (h2 : Float.beq b c = true) : Float.beq a c = true := by
  rw [float_beq_unpack] at h1 h2 ⊢
  exact beq_of_key (canonical_unpack _) (canonical_unpack _) (beq_ne_nan_left h1)
    (beq_ne_nan_right h2)
    ((key_of_beq (canonical_unpack _) (canonical_unpack _) h1).trans
      (key_of_beq (canonical_unpack _) (canonical_unpack _) h2))

/-- Two floats that compare `≤` both ways are IEEE-equal. -/
theorem float_beq_of_le_of_le {a b : Float} (h1 : Float.le a b = true)
    (h2 : Float.le b a = true) : Float.beq a b = true := by
  rw [float_le_unpack] at h1 h2
  rw [float_beq_unpack]
  exact beq_of_key (canonical_unpack _) (canonical_unpack _) (le_ne_nan_left h1)
    (le_ne_nan_right h1)
    (Int.le_antisymm (key_of_le (canonical_unpack _) (canonical_unpack _) h1)
      (key_of_le (canonical_unpack _) (canonical_unpack _) h2))

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

/-! ## `min` and `max` return an operand

Inside its range a clamp is the identity. The conclusion is IEEE equality
rather than `=`: on `+0 ≤ -0` the model returns `-0`, which is `beq` to
`+0` but not the same float. In the ordinary arm the result is the operand
the comparison picked, and when the comparison came back false the two
operands compare `≤` both ways. -/

/-- `min` is its left operand when that is at most the right one. -/
theorem tsMin_beq_left_of_le {a b : Float} (h : Float.le a b = true) :
    Float.beq (tsMin a b) a = true := by
  have hab := h
  rw [float_le_unpack] at hab
  have ha := le_ne_nan_left hab
  have hb := le_ne_nan_right hab
  unfold tsMin
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · exact float_beq_refl_of_ne_nan ha
  · rename_i sgn _ ha' hb'
    rw [float_beq_unpack, hb', ha']
    cases sgn <;> rfl
  · split
    · exact float_beq_refl_of_ne_nan ha
    · exact float_beq_of_le_of_le
        (float_le_of_not_lt_of_ne_nan ha hb (Bool.eq_false_iff.mpr ‹_›)) h

/-- `min` is its right operand when that is at most the left one. -/
theorem tsMin_beq_right_of_le {a b : Float} (h : Float.le b a = true) :
    Float.beq (tsMin a b) b = true := by
  have hba := h
  rw [float_le_unpack] at hba
  have hb := le_ne_nan_left hba
  have ha := le_ne_nan_right hba
  unfold tsMin
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · rename_i ha' hb'
    rw [float_beq_unpack, ha', hb']
    rename_i s; cases s <;> rfl
  · exact float_beq_refl_of_ne_nan hb
  · split
    · exact float_beq_of_le_of_le (float_le_of_lt ‹_›) h
    · exact float_beq_refl_of_ne_nan hb

/-- `max` is its right operand when the left one is at most it. -/
theorem tsMax_beq_right_of_le {a b : Float} (h : Float.le a b = true) :
    Float.beq (tsMax a b) b = true := by
  have hab := h
  rw [float_le_unpack] at hab
  have ha := le_ne_nan_left hab
  have hb := le_ne_nan_right hab
  unfold tsMax
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · rename_i ha' hb'
    rw [float_beq_unpack, ha', hb']
    rename_i s; cases s <;> rfl
  · exact float_beq_refl_of_ne_nan hb
  · split
    · exact float_beq_refl_of_ne_nan hb
    · exact float_beq_of_le_of_le h
        (float_le_of_not_lt_of_ne_nan ha hb (Bool.eq_false_iff.mpr ‹_›))

/-- `max` is its left operand when the right one is at most it. -/
theorem tsMax_beq_left_of_le {a b : Float} (h : Float.le b a = true) :
    Float.beq (tsMax a b) a = true := by
  have hba := h
  rw [float_le_unpack] at hba
  have hb := le_ne_nan_left hba
  have ha := le_ne_nan_right hba
  unfold tsMax
  split
  · exact absurd ‹_› ha
  · exact absurd ‹_› hb
  · exact float_beq_refl_of_ne_nan ha
  · rename_i sgn _ ha' hb'
    rw [float_beq_unpack, hb', ha']
    cases sgn <;> rfl
  · split
    · exact float_beq_of_le_of_le h (float_le_of_lt ‹_›)
    · exact float_beq_refl_of_ne_nan ha

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

/-- A shifted mantissa and its successor both fit in 53 bits: `k ≥ 1`
halves at least once. -/
theorem shift_succ_le_two53 {m k : Nat} (hm : m < 2 ^ 53) (hk : 1 ≤ k) :
    m >>> k + 1 ≤ 2 ^ 53 := by
  have h1 := shift_mul_le m k
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have h3 : (m >>> k) * 2 ≤ (m >>> k) * 2 ^ k := Nat.mul_le_mul_left _ h2
  omega

/-- Whichever way the arm bumps, the signed mantissa's magnitude stays
within `2^53`. -/
theorem natAbs_rounded_le (b : Bool) (s : Sign) {q : Nat} (hq : q + 1 ≤ 2 ^ 53) :
    (s.apply (if b = true then (q : Int) + 1 else (q : Int))).natAbs ≤ 2 ^ 53 := by
  cases s <;> cases b <;> simp only [Sign.apply, Int.natAbs_neg, ite_true, ite_false,
    Bool.false_eq_true] <;> omega

/-- `normalize_shape`'s cap holds for every rounding output: the magnitude
is at most `2^53` on exponent `0`. -/
theorem rounding_cap {M : Int} (h : M.natAbs ≤ 2 ^ 53) :
    totalExponent M.natAbs 0 ≤ 3900 := by
  unfold totalExponent
  have : M.natAbs.log2 < 54 := by
    rcases Nat.eq_zero_or_pos M.natAbs with hz | hp
    · rw [hz]; decide
    · exact (Nat.log2_lt (by omega)).mpr (by
        calc M.natAbs ≤ 2 ^ 53 := h
          _ < 2 ^ 54 := Nat.pow_lt_pow_right (by omega) (by omega))
  omega

/-- What every rounding hands to `pack`: a round shape that is not NaN.
The non-finite arms return the input, which is canonical; the finite arm
is a `normalize` under the cap. -/
theorem roundIntegral_shape (dir : RoundDir) {u : UnpackedFloat} (hu : Canonical u)
    (hn : u ≠ .notANumber) :
    RoundShape (roundIntegral .binary64 dir u) ∧ roundIntegral .binary64 dir u ≠ .notANumber := by
  cases hu with
  | notANumber => exact absurd rfl hn
  | infinity s => exact ⟨.canonical (.infinity s), fun h => UnpackedFloat.noConfusion h⟩
  | zero s => exact ⟨.canonical (.zero s), fun h => UnpackedFloat.noConfusion h⟩
  | subnormal s m hm hmlt =>
    dsimp only [roundIntegral]
    split
    · exact ⟨.canonical (.subnormal s m hm hmlt), fun h => UnpackedFloat.noConfusion h⟩
    · apply normalize_shape
      apply rounding_cap
      exact natAbs_rounded_le _ s
        (shift_succ_le_two53 (by omega : m < 2 ^ 53) (by omega : 1 ≤ (-(-1074 : Int)).toNat))
  | normal s m e hm hlo hhi helo hehi =>
    dsimp only [roundIntegral]
    split
    · exact ⟨.canonical (.normal s m e hm hlo hhi helo hehi), fun h => UnpackedFloat.noConfusion h⟩
    · rename_i he
      apply normalize_shape
      apply rounding_cap
      exact natAbs_rounded_le _ s (shift_succ_le_two53 hhi (by omega : 1 ≤ (-e).toNat))

/-- Unpacking a rounded float is unpacking the pack of the rounded
unpacking: the spelling `key_unpack_pack_mono` crosses. -/
theorem unpack_tsFloor (x : Float) :
    (tsFloor x).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64
          (roundIntegral .binary64 .towardNegInf x.toModel.unpack)) := rfl

theorem unpack_tsCeil (x : Float) :
    (tsCeil x).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64
          (roundIntegral .binary64 .towardPosInf x.toModel.unpack)) := rfl

/-- `Math.floor` never exceeds its input. -/
theorem tsFloor_le {x : Float} (hx : x.toModel.unpack ≠ .notANumber) :
    Float.le (tsFloor x) x = true := by
  have hc : Canonical x.toModel.unpack := canonical_unpack _
  rw [float_le_unpack, unpack_tsFloor]
  obtain ⟨hshape, hnn⟩ := roundIntegral_shape .towardNegInf hc hx
  have hkey : key (roundIntegral .binary64 .towardNegInf x.toModel.unpack)
      ≤ key x.toModel.unpack := by
    generalize x.toModel.unpack = u at hc hx ⊢
    cases hc with
    | notANumber => exact absurd rfl hx
    | infinity s => exact Int.le_refl _
    | zero s => exact Int.le_refl _
    | subnormal s m hm hmlt => exact key_floor_finite_le (.subnormal s m hm hmlt)
    | normal s m e hm hlo hhi helo hehi =>
      exact key_floor_finite_le (.normal s m e hm hlo hhi helo hehi)
  have hmono := key_unpack_pack_mono hshape (.canonical hc) hnn hx hkey
  rw [unpack_pack_of_canonical hc] at hmono
  exact le_of_key (canonical_unpack _) hc (unpack_pack_ne_nan hshape hnn) hx hmono

/-- `Math.ceil` never falls below its input. -/
theorem tsCeil_ge {x : Float} (hx : x.toModel.unpack ≠ .notANumber) :
    Float.le x (tsCeil x) = true := by
  have hc : Canonical x.toModel.unpack := canonical_unpack _
  rw [float_le_unpack, unpack_tsCeil]
  obtain ⟨hshape, hnn⟩ := roundIntegral_shape .towardPosInf hc hx
  have hkey : key x.toModel.unpack
      ≤ key (roundIntegral .binary64 .towardPosInf x.toModel.unpack) := by
    generalize x.toModel.unpack = u at hc hx ⊢
    cases hc with
    | notANumber => exact absurd rfl hx
    | infinity s => exact Int.le_refl _
    | zero s => exact Int.le_refl _
    | subnormal s m hm hmlt => exact key_ceil_finite_ge (.subnormal s m hm hmlt)
    | normal s m e hm hlo hhi helo hehi =>
      exact key_ceil_finite_ge (.normal s m e hm hlo hhi helo hehi)
  have hmono := key_unpack_pack_mono (.canonical hc) hshape hx hnn hkey
  rw [unpack_pack_of_canonical hc] at hmono
  exact le_of_key hc (canonical_unpack _) hx (unpack_pack_ne_nan hshape hnn) hmono

/-! `Math.trunc` is floor on the non-negative side and ceil on the
non-positive side — not an inequality but an equation, so the floor and
ceil facts carry over. On a positive-signed input trunc's and floor's
`bump` are both `false`, so the unpacked results are the same term; the
zeros and the infinities round to themselves in every direction. -/

/-- On a positive-signed unpacking, toward-zero and toward-negative-infinity agree. -/
theorem roundIntegral_towardZero_eq_negInf_of_positive (m : Nat) (e : Int) (h : 0 < m) :
    roundIntegral .binary64 .towardZero (.finite .positive m e h)
      = roundIntegral .binary64 .towardNegInf (.finite .positive m e h) := by
  dsimp only [roundIntegral]

/-- On a negative-signed unpacking, toward-zero and toward-positive-infinity agree. -/
theorem roundIntegral_towardZero_eq_posInf_of_negative (m : Nat) (e : Int) (h : 0 < m) :
    roundIntegral .binary64 .towardZero (.finite .negative m e h)
      = roundIntegral .binary64 .towardPosInf (.finite .negative m e h) := by
  dsimp only [roundIntegral]

theorem tsTrunc_eq_tsFloor_of_nonneg {x : Float} (h : Float.le 0 x = true) :
    tsTrunc x = tsFloor x := by
  have h' := h
  rw [float_le_unpack, show (0 : Float).toModel.unpack = UnpackedFloat.zero .positive from rfl] at h'
  have hc : Canonical x.toModel.unpack := canonical_unpack _
  have hk := key_of_le (.zero .positive) hc h'
  unfold tsTrunc tsFloor
  congr 2
  generalize x.toModel.unpack = u at hc hk h' ⊢
  cases hc with
  | notANumber => exact absurd rfl (le_ne_nan_right h')
  | infinity s =>
    have hs := sign_of_inf_key_nonneg (show (0 : Int) ≤ _ from hk)
    subst hs
    rfl
  | zero s => cases s <;> rfl
  | subnormal s m hm hmlt =>
    have hs := sign_of_key_nonneg (show (0 : Int) ≤ _ from hk)
    subst hs
    exact roundIntegral_towardZero_eq_negInf_of_positive m _ hm
  | normal s m e hm hlo hhi helo hehi =>
    have hs := sign_of_key_nonneg (show (0 : Int) ≤ _ from hk)
    subst hs
    exact roundIntegral_towardZero_eq_negInf_of_positive m e hm

theorem tsTrunc_eq_tsCeil_of_nonpos {x : Float} (h : Float.le x 0 = true) :
    tsTrunc x = tsCeil x := by
  have h' := h
  rw [float_le_unpack, show (0 : Float).toModel.unpack = UnpackedFloat.zero .positive from rfl] at h'
  have hc : Canonical x.toModel.unpack := canonical_unpack _
  have hk := key_of_le hc (.zero .positive) h'
  unfold tsTrunc tsCeil
  congr 2
  generalize x.toModel.unpack = u at hc hk h' ⊢
  cases hc with
  | notANumber => exact absurd rfl (le_ne_nan_left h')
  | infinity s =>
    cases s with
    | positive =>
      exfalso
      have := HUGE_pos
      simp only [key, Sign.apply] at hk
      omega
    | negative => rfl
  | zero s => cases s <;> rfl
  | subnormal s m hm hmlt =>
    cases s with
    | positive =>
      exfalso
      rw [key_finite_cast] at hk
      have := Nat.mul_pos hm (Nat.two_pow_pos ((-1074 : Int) + 1074).toNat)
      simp only [Sign.apply, key] at hk
      omega
    | negative => exact roundIntegral_towardZero_eq_posInf_of_negative m _ hm
  | normal s m e hm hlo hhi helo hehi =>
    cases s with
    | positive =>
      exfalso
      rw [key_finite_cast] at hk
      have := Nat.mul_pos hm (Nat.two_pow_pos (e + 1074).toNat)
      simp only [Sign.apply, key] at hk
      omega
    | negative => exact roundIntegral_towardZero_eq_posInf_of_negative m e hm

/-! ## Strict bounds propagate through every rounding

A rounding's finite arm has magnitude at most `2^53` on exponent `0`, so
its key sits between the keys of `∓2^53`, two canonical values built by
hand. Their keys stay symbolic: evaluating `2^1075` trips the
exponentiation threshold and the recursion limit. The non-finite arms
return the input, whose bound is the hypothesis. -/

theorem canonical_two53_pos : Canonical (.finite .positive (2 ^ 52) 1 (Nat.two_pow_pos 52)) :=
  .normal .positive (2 ^ 52) 1 (Nat.two_pow_pos 52) (Nat.le_refl _) pow52_lt_53 (by decide) (by decide)

theorem canonical_two53_neg : Canonical (.finite .negative (2 ^ 52) 1 (Nat.two_pow_pos 52)) :=
  .normal .negative (2 ^ 52) 1 (Nat.two_pow_pos 52) (Nat.le_refl _) pow52_lt_53 (by decide) (by decide)

/-- A rounded mantissa of at least `-2^53` normalizes to a key at least
the negative anchor's. -/
theorem key_normalize_rounding_ge {M : Int} (hM : -(2 ^ 53 : Int) ≤ M) (z : Sign) :
    key (.finite .negative (2 ^ 52) 1 (Nat.two_pow_pos 52))
      ≤ key (UnpackedFloat.normalize .binary64 M 0 z) := by
  rw [← normalize_canonical_self canonical_two53_neg]
  apply key_normalize_mono_value _ _ _ (by decide) (by decide)
  have e1 : ((1 : Int) + 1074).toNat = 1074 + 1 := by decide
  have e0 : ((0 : Int) + 1074).toNat = 1074 := by decide
  rw [e1, e0, int_pow_split 1074 1]
  have : Sign.apply .negative ((2 ^ 52 : Nat) : Int) * (2 ^ 1074 * 2 ^ 1)
      = (-(2 ^ 53 : Int)) * 2 ^ 1074 := by
    simp only [Sign.apply]
    rw [Int.mul_comm (2 ^ 1074) (2 ^ 1), ← Int.mul_assoc]
    congr 1
  rw [this]
  exact Int.mul_le_mul_of_nonneg_right hM (Int.le_of_lt (intPow_pos _))

/-- A rounded mantissa of at most `2^53` normalizes to a key at most the
positive anchor's. -/
theorem key_normalize_rounding_le {M : Int} (hM : M ≤ (2 ^ 53 : Int)) (z : Sign) :
    key (UnpackedFloat.normalize .binary64 M 0 z)
      ≤ key (.finite .positive (2 ^ 52) 1 (Nat.two_pow_pos 52)) := by
  rw [← normalize_canonical_self canonical_two53_pos]
  apply key_normalize_mono_value _ _ _ (by decide) (by decide)
  have e1 : ((1 : Int) + 1074).toNat = 1074 + 1 := by decide
  have e0 : ((0 : Int) + 1074).toNat = 1074 := by decide
  rw [e1, e0, int_pow_split 1074 1]
  have : Sign.apply .positive ((2 ^ 52 : Nat) : Int) * (2 ^ 1074 * 2 ^ 1)
      = (2 ^ 53 : Int) * 2 ^ 1074 := by
    simp only [Sign.apply]
    rw [Int.mul_comm (2 ^ 1074) (2 ^ 1), ← Int.mul_assoc]
    congr 1
  rw [this]
  exact Int.mul_le_mul_of_nonneg_right hM (Int.le_of_lt (intPow_pos _))

/-- Whichever way the arm bumps, the signed mantissa is within `∓2^53`. -/
theorem rounded_mantissa_bounds (b : Bool) (s : Sign) {q : Nat} (hq : q + 1 ≤ 2 ^ 53) :
    -(2 ^ 53 : Int) ≤ s.apply (if b = true then (q : Int) + 1 else (q : Int))
      ∧ s.apply (if b = true then (q : Int) + 1 else (q : Int)) ≤ 2 ^ 53 := by
  have h := natAbs_rounded_le b s hq
  omega

/-- The rounded arm, packed, is strictly above `-∞`. -/
theorem lt_neg_inf_normalize_rounded (s : Sign) (b : Bool) {q : Nat} (hq : q + 1 ≤ 2 ^ 53) :
    UnpackedFloat.lt (.infinity .negative)
      (unpack .binary64 (UnpackedFloat.pack .binary64
        (UnpackedFloat.normalize .binary64
          (s.apply (if b = true then (q : Int) + 1 else (q : Int))) 0 s))) = true := by
  obtain ⟨hsh, hnn⟩ := normalize_shape _ _ _ (rounding_cap (natAbs_rounded_le b s hq))
  have hb := rounded_mantissa_bounds b s hq
  have hmono := key_unpack_pack_mono (.canonical canonical_two53_neg) hsh
    (fun hh => UnpackedFloat.noConfusion hh) hnn (key_normalize_rounding_ge hb.1 s)
  rw [unpack_pack_of_canonical canonical_two53_neg] at hmono
  exact lt_of_key (.infinity .negative) (canonical_unpack _)
    (fun hh => UnpackedFloat.noConfusion hh) (unpack_pack_ne_nan hsh hnn)
    (Int.lt_of_lt_of_le
      (key_lt_HUGE canonical_two53_neg (fun _ hh => UnpackedFloat.noConfusion hh)).2 hmono)

/-- The rounded arm, packed, is strictly below `+∞`. -/
theorem normalize_rounded_lt_pos_inf (s : Sign) (b : Bool) {q : Nat} (hq : q + 1 ≤ 2 ^ 53) :
    UnpackedFloat.lt
      (unpack .binary64 (UnpackedFloat.pack .binary64
        (UnpackedFloat.normalize .binary64
          (s.apply (if b = true then (q : Int) + 1 else (q : Int))) 0 s)))
      (.infinity .positive) = true := by
  obtain ⟨hsh, hnn⟩ := normalize_shape _ _ _ (rounding_cap (natAbs_rounded_le b s hq))
  have hb := rounded_mantissa_bounds b s hq
  have hmono := key_unpack_pack_mono hsh (.canonical canonical_two53_pos) hnn
    (fun hh => UnpackedFloat.noConfusion hh) (key_normalize_rounding_le hb.2 s)
  rw [unpack_pack_of_canonical canonical_two53_pos] at hmono
  exact lt_of_key (canonical_unpack _) (.infinity .positive)
    (unpack_pack_ne_nan hsh hnn) (fun hh => UnpackedFloat.noConfusion hh)
    (Int.lt_of_le_of_lt hmono
      (key_lt_HUGE canonical_two53_pos (fun _ hh => UnpackedFloat.noConfusion hh)).1)

/-- Unpacking any rounded float. -/
theorem unpack_rounded (dir : RoundDir) (x : Float) :
    (Float.ofModel (Float.Model.pack (roundIntegral .binary64 dir x.toModel.unpack))).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64
          (roundIntegral .binary64 dir x.toModel.unpack)) := rfl

theorem rounding_lo (dir : RoundDir) {x : Float} (hLo : (-(1.0 / 0.0) : Float) < x) :
    (-(1.0 / 0.0) : Float)
      < Float.ofModel (Float.Model.pack (roundIntegral .binary64 dir x.toModel.unpack)) := by
  have h : Float.lt (-(1.0 / 0.0)) x = true := hLo
  rw [float_lt_unpack,
    show ((-(1.0 / 0.0) : Float)).toModel.unpack = UnpackedFloat.infinity .negative from rfl] at h
  have hx := lt_ne_nan_right h
  have hc : Canonical x.toModel.unpack := canonical_unpack _
  show Float.lt _ _ = true
  rw [float_lt_unpack, unpack_rounded,
    show ((-(1.0 / 0.0) : Float)).toModel.unpack = UnpackedFloat.infinity .negative from rfl]
  generalize x.toModel.unpack = u at hc hx h ⊢
  cases hc with
  | notANumber => exact absurd rfl hx
  | infinity s =>
    cases s
    · exact absurd h (by decide)
    · dsimp only [roundIntegral]; decide
  | zero s => cases s <;> (dsimp only [roundIntegral]; decide)
  | subnormal s m hm hmlt =>
    dsimp only [roundIntegral]
    split
    · rw [unpack_pack_of_canonical (.subnormal s m hm hmlt)]; exact h
    · exact lt_neg_inf_normalize_rounded s _ (shift_succ_le_two53 (by omega) (by omega))
  | normal s m e hm hlo hhi helo hehi =>
    dsimp only [roundIntegral]
    split
    · rw [unpack_pack_of_canonical (.normal s m e hm hlo hhi helo hehi)]; exact h
    · exact lt_neg_inf_normalize_rounded s _ (shift_succ_le_two53 hhi (by omega))

theorem rounding_hi (dir : RoundDir) {x : Float} (hHi : x < (1.0 / 0.0 : Float)) :
    Float.ofModel (Float.Model.pack (roundIntegral .binary64 dir x.toModel.unpack))
      < (1.0 / 0.0 : Float) := by
  have h : Float.lt x (1.0 / 0.0) = true := hHi
  rw [float_lt_unpack,
    show ((1.0 / 0.0 : Float)).toModel.unpack = UnpackedFloat.infinity .positive from rfl] at h
  have hx := lt_ne_nan_left h
  have hc : Canonical x.toModel.unpack := canonical_unpack _
  show Float.lt _ _ = true
  rw [float_lt_unpack, unpack_rounded,
    show ((1.0 / 0.0 : Float)).toModel.unpack = UnpackedFloat.infinity .positive from rfl]
  generalize x.toModel.unpack = u at hc hx h ⊢
  cases hc with
  | notANumber => exact absurd rfl hx
  | infinity s =>
    cases s
    · dsimp only [roundIntegral]; decide
    · exact absurd h (by decide)
  | zero s => cases s <;> (dsimp only [roundIntegral]; decide)
  | subnormal s m hm hmlt =>
    dsimp only [roundIntegral]
    split
    · rw [unpack_pack_of_canonical (.subnormal s m hm hmlt)]; exact h
    · exact normalize_rounded_lt_pos_inf s _ (shift_succ_le_two53 (by omega) (by omega))
  | normal s m e hm hlo hhi helo hehi =>
    dsimp only [roundIntegral]
    split
    · rw [unpack_pack_of_canonical (.normal s m e hm hlo hhi helo hehi)]; exact h
    · exact normalize_rounded_lt_pos_inf s _ (shift_succ_le_two53 hhi (by omega))

theorem tsFloor_lo {x : Float} (h : (-(1.0 / 0.0) : Float) < x) :
    (-(1.0 / 0.0) : Float) < tsFloor x :=
  rounding_lo .towardNegInf h
theorem tsFloor_hi {x : Float} (h : x < (1.0 / 0.0 : Float)) : tsFloor x < (1.0 / 0.0 : Float) :=
  rounding_hi .towardNegInf h
theorem tsCeil_lo {x : Float} (h : (-(1.0 / 0.0) : Float) < x) :
    (-(1.0 / 0.0) : Float) < tsCeil x :=
  rounding_lo .towardPosInf h
theorem tsCeil_hi {x : Float} (h : x < (1.0 / 0.0 : Float)) : tsCeil x < (1.0 / 0.0 : Float) :=
  rounding_hi .towardPosInf h
theorem tsTrunc_lo {x : Float} (h : (-(1.0 / 0.0) : Float) < x) :
    (-(1.0 / 0.0) : Float) < tsTrunc x :=
  rounding_lo .towardZero h
theorem tsTrunc_hi {x : Float} (h : x < (1.0 / 0.0 : Float)) : tsTrunc x < (1.0 / 0.0 : Float) :=
  rounding_hi .towardZero h
theorem tsRound_lo {x : Float} (h : (-(1.0 / 0.0) : Float) < x) :
    (-(1.0 / 0.0) : Float) < tsRound x :=
  rounding_lo .nearestHalfUp h
theorem tsRound_hi {x : Float} (h : x < (1.0 / 0.0 : Float)) : tsRound x < (1.0 / 0.0 : Float) :=
  rounding_hi .nearestHalfUp h

end Js.Number.FloatOpsFacts
