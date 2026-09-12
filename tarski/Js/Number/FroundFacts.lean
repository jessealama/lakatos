import Js.Number.FloatFacts
import Js.Number.FloatOps

/-!
Order theory for `Math.fround`. The narrowing rounds at binary32, tests
the exponent for overflow, and rounds back at binary64. Each stage is
monotone on values, so the composite is, and every order fact the
symbolic rungs need is that one theorem instantiated at a constant.
-/

namespace Js.Number.FroundFacts

open Float.Model Float.Model.UnpackedFloat Js.Number.FloatFacts Js.Number.FloatOps

/-! ## Groundwork -/

/-- `round`'s pre-shift leaves the grid where it was: it multiplies the
mantissa and divides the exponent by the same power. -/
theorem gridF_preshift (spec : Format) {m : Nat} (hm : 0 < m) (e : Int) :
    gridF spec (m * 2 ^ (e - gridF spec m e).toNat) (e - ((e - gridF spec m e).toNat : Int))
      = gridF spec m e := by
  simp only [gridF, Format.targetExponent, totalExponent]
  rw [log2_mul_pow hm]
  omega

theorem rnShiftF_id (m : Nat) : rnShiftF m 0 0 1 = m := by
  have hlt : (m % 2 ^ 0 * 1 + 0) * 2 < 2 ^ 0 * 1 := by simp [Nat.mod_one]
  rw [rnShiftF_of_lt hlt]
  simp

theorem key_neg (u : UnpackedFloat) : key u.neg = -key u := by
  cases u <;> simp [key, UnpackedFloat.neg, sign_apply_neg]

theorem gridF32_ge (m : Nat) (e : Int) : (-149 : Int) ≤ gridF .binary32 m e := by
  have := gridF_ge .binary32 m e
  have h : Format.binary32.minExponent = -149 := by decide
  omega

/-- Two magnitudes compared at the binary64 quantum, rescaled to their own
common exponent: the form the rounding lemmas take their hypothesis in. -/
theorem scaled_of_key {m₁ m₂ : Nat} {e₁ e₂ : Int} (he₁ : (-1074 : Int) ≤ e₁)
    (he₂ : (-1074 : Int) ≤ e₂)
    (h : (m₁ : Int) * 2 ^ (e₁ + 1074).toNat ≤ (m₂ : Int) * 2 ^ (e₂ + 1074).toNat) :
    m₁ * 2 ^ (e₁ - min e₁ e₂).toNat ≤ m₂ * 2 ^ (e₂ - min e₁ e₂).toNat := by
  have hnat : m₁ * 2 ^ (e₁ + 1074).toNat ≤ m₂ * 2 ^ (e₂ + 1074).toNat := by
    have hc₁ : ((m₁ * 2 ^ (e₁ + 1074).toNat : Nat) : Int)
        = (m₁ : Int) * 2 ^ (e₁ + 1074).toNat := by
      rw [Int.natCast_mul, Int.natCast_pow]; rfl
    have hc₂ : ((m₂ * 2 ^ (e₂ + 1074).toNat : Nat) : Int)
        = (m₂ : Int) * 2 ^ (e₂ + 1074).toNat := by
      rw [Int.natCast_mul, Int.natCast_pow]; rfl
    omega
  have hsplit₁ : (e₁ + 1074).toNat = (e₁ - min e₁ e₂).toNat + (min e₁ e₂ + 1074).toNat := by
    omega
  have hsplit₂ : (e₂ + 1074).toNat = (e₂ - min e₁ e₂).toNat + (min e₁ e₂ + 1074).toNat := by
    omega
  rw [hsplit₁, hsplit₂, Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc, ← Nat.mul_assoc] at hnat
  exact Nat.le_of_mul_le_mul_right hnat (Nat.two_pow_pos _)

/-! ## What binary32 rounding produces -/

/-- The shape of a binary32 rounding at a given sign: a zero, or a finite
value whose mantissa fits binary32 and whose exponent is at or above the
subnormal floor, normal whenever it is above that floor. -/
inductive Narrowed32 (s : Sign) : UnpackedFloat → Prop
  | zero : Narrowed32 s (.zero s)
  | finite (m : Nat) (e : Int) (h : 0 < m) (hm : m < 2 ^ 24) (he : (-149 : Int) ≤ e)
      (hn : (-148 : Int) ≤ e → 2 ^ 23 ≤ m) : Narrowed32 s (.finite s m e h)

theorem narrowed32_cases {s : Sign} {w : UnpackedFloat} (h : Narrowed32 s w) :
    w = .zero s ∨ ∃ (m : Nat) (e : Int) (hp : 0 < m),
      w = .finite s m e hp ∧ m < 2 ^ 24 ∧ (-149 : Int) ≤ e
        ∧ ((-148 : Int) ≤ e → 2 ^ 23 ≤ m) := by
  cases h with
  | zero => exact Or.inl rfl
  | finite m e hp hm he hn => exact Or.inr ⟨m, e, hp, rfl, hm, he, hn⟩

/-- Above the subnormal floor the rounded mantissa is normal. -/
theorem rnShiftF32_ge_normal {m : Nat} (hm : 0 < m) (e : Int)
    (hw : WellPlacedF .binary32 m e) (hg : (-149 : Int) < gridF .binary32 m e) :
    2 ^ 23 ≤ rnShiftF m ((gridF .binary32 m e - e).toNat) 0 1 := by
  have hmb : ((Format.binary32.mantissaBits : Nat) : Int) = 24 := by decide
  have hme : Format.binary32.minExponent = -149 := by decide
  have hg' : gridF .binary32 m e = totalExponent m e - 24 := by
    simp only [gridF, Format.targetExponent, hmb, hme] at hg ⊢
    omega
  have hlog : 23 ≤ m.log2 := by
    simp only [WellPlacedF, hg', totalExponent] at hw
    omega
  have hshift : (gridF .binary32 m e - e).toNat = m.log2 - 23 := by
    simp only [hg', totalExponent]
    omega
  have hb := (rnShiftF_bounds m ((gridF .binary32 m e - e).toNat) 0 1).1
  have hq : 2 ^ 23 ≤ m / 2 ^ ((gridF .binary32 m e - e).toNat) := by
    rw [hshift, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    have hsum : 23 + (m.log2 - 23) = m.log2 := by omega
    rw [hsum]
    exact Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hm)
  omega

theorem roundWA32_narrowed (s : Sign) {m : Nat} (hm : 0 < m) (e : Int)
    (hw : WellPlacedF .binary32 m e) :
    Narrowed32 s (roundWithAccuracy .binary32 s m e (accuracyOfFraction 0 1)) := by
  have hge := gridF32_ge m e
  have hle : rnShiftF m ((gridF .binary32 m e - e).toNat) 0 1 ≤ 2 ^ 24 := by
    have h := rnShiftF_leF .binary32 m e 0 1 hw
    have hmb : Format.binary32.mantissaBits = 24 := by decide
    rw [hmb] at h
    exact h
  rw [roundWA_eqF .binary32 23 (by decide) s m e 0 1 hw Nat.one_pos Nat.zero_lt_one]
  split
  · exact .finite (2 ^ 23) (gridF .binary32 m e + 1) (Nat.two_pow_pos 23)
      (by omega) (by omega) (fun _ => Nat.le_refl _)
  · rename_i hne
    split
    · exact .zero
    · rename_i hnz
      exact .finite _ (gridF .binary32 m e) (Nat.pos_of_ne_zero hnz) (by omega) hge
        (fun hb => rnShiftF32_ge_normal hm e hw (by omega))

theorem round32_narrowed (s : Sign) {m : Nat} (hm : 0 < m) (e : Int) :
    Narrowed32 s (UnpackedFloat.round .binary32 s m e) := by
  rw [round_eq_roundWAF]
  exact roundWA32_narrowed s (Nat.mul_pos hm (Nat.two_pow_pos _)) _
    (wellPlaced_round_inputF .binary32 hm e)

/-! ## The binary64 rounding that widens the result back -/

/-- A value carrying at most 24 significant bits, well above the binary64
subnormal floor, is already a binary64 value: rounding it there changes
nothing. This is what lets the narrowing's last stage drop out of the
order argument. -/
theorem key_round64_exact_pos {m : Nat} (hm : 0 < m) (e : Int)
    (hmle : m < 2 ^ 24) (he : (-149 : Int) ≤ e) :
    key (UnpackedFloat.round .binary64 .positive m e) = (m : Int) * 2 ^ (e + 1074).toNat := by
  have hmb : ((Format.binary64.mantissaBits : Nat) : Int) = 53 := by decide
  have hme : Format.binary64.minExponent = -1074 := by decide
  have hlog : m.log2 ≤ 24 := by
    have h1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hm)
    have h2 : (2 : Nat) ^ m.log2 ≤ 2 ^ 24 := by omega
    exact (Nat.pow_le_pow_iff_right (by omega)).mp h2
  have hg : gridF .binary64 m e = (m.log2 : Int) + e - 52 := by
    simp only [gridF, Format.targetExponent, totalExponent, hmb, hme]
    omega
  have hk : (e - gridF .binary64 m e).toNat = 52 - m.log2 := by
    rw [hg]; omega
  have hm₀ : 0 < m * 2 ^ (e - gridF .binary64 m e).toNat :=
    Nat.mul_pos hm (Nat.two_pow_pos _)
  have hgrid₀ : gridF .binary64 (m * 2 ^ (e - gridF .binary64 m e).toNat)
      (e - ((e - gridF .binary64 m e).toNat : Int)) = gridF .binary64 m e :=
    gridF_preshift .binary64 hm e
  have hshift :
      (gridF .binary64 m e - (e - ((e - gridF .binary64 m e).toNat : Int))).toNat = 0 := by
    omega
  rw [round_eq_roundWAF,
    key_roundWA_posF .binary64 52 (by decide) (by decide) _ _ 0 1
      (wellPlaced_round_inputF .binary64 hm e) Nat.one_pos Nat.zero_lt_one,
    hgrid₀, hshift, rnShiftF_id]
  rw [hk, hg]
  have hcast : ((m * 2 ^ (52 - m.log2) : Nat) : Int) = (m : Int) * 2 ^ (52 - m.log2) := by
    rw [Int.natCast_mul, Int.natCast_pow]; rfl
  rw [hcast, Int.mul_assoc, ← Int.pow_add]
  have hsum : (52 - m.log2) + ((m.log2 : Int) + e - 52 + 1074).toNat = (e + 1074).toNat := by
    omega
  rw [hsum]

/-! ## The narrowing, at the key layer -/

/-- The magnitude the narrowing reaches before the overflow test. -/
def mag32 (m : Nat) (e : Int) : Int := key (UnpackedFloat.round .binary32 .positive m e)

/-- The overflow test, read as a cut on magnitudes. A binary32 value at
exponent 105 or above carries a normal mantissa, so it is at least
`2 ^ 23 * 2 ^ (105 + 1074)`; one below that exponent is under the same
bound, its mantissa being short of `2 ^ 24`. -/
def clamp32 (k : Int) : Int := if 2 ^ 1202 ≤ k then HUGE else k

theorem natCast_two_pow (n : Nat) : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by
  rw [Int.natCast_pow]; rfl

theorem int_two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n := by
  rw [show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow]
  have := Nat.two_pow_pos n
  omega

theorem cut_le_HUGE : (2 : Int) ^ 1202 ≤ HUGE := by
  have hnat : (2 : Nat) ^ 1202 ≤ 2 ^ 6000 := Nat.pow_le_pow_right (by omega) (by omega)
  have h := Int.ofNat_le.mpr hnat
  rw [natCast_two_pow, natCast_two_pow] at h
  simpa only [HUGE] using h

theorem clamp32_mono {k₁ k₂ : Int} (h : k₁ ≤ k₂) : clamp32 k₁ ≤ clamp32 k₂ := by
  have hH := cut_le_HUGE
  simp only [clamp32]
  split <;> split <;> omega

theorem clamp32_le_HUGE (k : Int) : clamp32 k ≤ HUGE := by
  have := cut_le_HUGE
  simp only [clamp32]
  split <;> omega

theorem clamp32_nonneg {k : Int} (h : 0 ≤ k) : 0 ≤ clamp32 k := by
  have := HUGE_pos
  simp only [clamp32]
  split <;> omega

/-- At exponent 105 or above a normal binary32 mantissa clears the cut. -/
theorem cut_of_normal {m : Nat} {e : Int} (hm : 2 ^ 23 ≤ m) (he : (105 : Int) ≤ e) :
    (2 : Int) ^ 1202 ≤ (m : Int) * 2 ^ (e + 1074).toNat := by
  have ht : 1179 ≤ (e + 1074).toNat := by omega
  have hnat : (2 : Nat) ^ 1202 ≤ m * 2 ^ (e + 1074).toNat := by
    calc (2 : Nat) ^ 1202 = 2 ^ 23 * 2 ^ 1179 := by rw [← Nat.pow_add]
      _ ≤ m * 2 ^ (e + 1074).toNat :=
          Nat.mul_le_mul hm (Nat.pow_le_pow_right (by omega) ht)
  have h := Int.ofNat_le.mpr hnat
  rw [natCast_two_pow, Int.natCast_mul, natCast_two_pow] at h
  exact h

/-- Below that exponent the mantissa is short of `2 ^ 24`, so the value
stays under the cut. -/
theorem below_cut {m : Nat} {e : Int} (hm : m < 2 ^ 24) (he : ¬ ((105 : Int) ≤ e))
    (hge : (-149 : Int) ≤ e) :
    (m : Int) * 2 ^ (e + 1074).toNat < (2 : Int) ^ 1202 := by
  have ht : (e + 1074).toNat ≤ 1178 := by omega
  have hnat : m * 2 ^ (e + 1074).toNat < 2 ^ 1202 := by
    calc m * 2 ^ (e + 1074).toNat ≤ m * 2 ^ 1178 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ht)
      _ < 2 ^ 24 * 2 ^ 1178 := by
          exact Nat.mul_lt_mul_right (Nat.two_pow_pos 1178) |>.mpr hm
      _ = 2 ^ 1202 := by rw [← Nat.pow_add]
  have h := Int.ofNat_lt.mpr hnat
  rw [natCast_two_pow, Int.natCast_mul, natCast_two_pow] at h
  exact h

theorem mag32_nonneg {m : Nat} (hm : 0 < m) (e : Int) : 0 ≤ mag32 m e := by
  simp only [mag32]
  rw [round_eq_roundWAF,
    key_roundWA_posF .binary32 23 (by decide) (by decide) _ _ 0 1
      (wellPlaced_round_inputF .binary32 hm e) Nat.one_pos Nat.zero_lt_one]
  exact natCast_mul_intPow_nonneg _ _

/-- Binary32 rounding is monotone, read through `mag32`. -/
theorem mag32_mono {m₁ m₂ : Nat} {e₁ e₂ : Int} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (he₁ : (-1074 : Int) ≤ e₁) (he₂ : (-1074 : Int) ≤ e₂)
    (h : (m₁ : Int) * 2 ^ (e₁ + 1074).toNat ≤ (m₂ : Int) * 2 ^ (e₂ + 1074).toNat) :
    mag32 m₁ e₁ ≤ mag32 m₂ e₂ :=
  key_round32_pos_mono h₁ h₂ (scaled_of_key he₁ he₂ h)

/-! ## The narrowing's key -/

theorem fround_of_zero {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hr : UnpackedFloat.round .binary32 s m e = .zero s) :
    froundUnpacked (.finite s m e h) = .zero s := by
  simp only [froundUnpacked, hr]

theorem fround_of_finite {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    {m' : Nat} {e' : Int} {h' : 0 < m'}
    (hr : UnpackedFloat.round .binary32 s m e = .finite s m' e' h') :
    froundUnpacked (.finite s m e h)
      = if 105 ≤ e' then .infinity s else UnpackedFloat.round .binary64 s m' e' := by
  simp only [froundUnpacked, hr]

/-- Binary32 rounding threads the sign through untouched. -/
theorem round32_neg (m : Nat) (e : Int) :
    UnpackedFloat.round .binary32 .negative m e
      = (UnpackedFloat.round .binary32 .positive m e).neg := by
  simp only [UnpackedFloat.round, roundWithAccuracy, UnpackedFloat.neg]
  split <;> rfl

/-- The narrowing's key on a positive finite input: the binary32 rounding's
magnitude, cut at the overflow line. -/
theorem key_fround_finite_pos {m : Nat} (hm : 0 < m) (e : Int) :
    key (froundUnpacked (.finite .positive m e hm)) = clamp32 (mag32 m e) := by
  rcases narrowed32_cases (round32_narrowed .positive hm e) with hz | ⟨m', e', hp, hr, hmlt, hge, hn⟩
  · rw [fround_of_zero hz]
    have hz0 : mag32 m e = 0 := by simp only [mag32, hz, key]
    have hpz := int_two_pow_pos 1202
    simp only [key, clamp32, hz0]
    rw [if_neg (by omega : ¬ ((2 : Int) ^ 1202 ≤ 0))]
  · rw [fround_of_finite hr]
    have hmag : mag32 m e = (m' : Int) * 2 ^ (e' + 1074).toNat := by
      simp only [mag32, hr, key, Sign.apply]
    by_cases hbig : (105 : Int) ≤ e'
    · -- Above the cut: a normal mantissa at exponent 105 or more.
      have hcut : (2 : Int) ^ 1202 ≤ mag32 m e := by
        rw [hmag]; exact cut_of_normal (hn (by omega)) hbig
      rw [if_pos hbig]
      simp only [key, Sign.apply, clamp32, if_pos hcut]
    · -- Below the cut: the widening is exact and the magnitude survives.
      have hcut : ¬ ((2 : Int) ^ 1202 ≤ mag32 m e) := by
        rw [hmag]
        have := below_cut hmlt hbig hge
        omega
      rw [if_neg hbig, key_round64_exact_pos hp e' hmlt hge, clamp32, if_neg hcut, hmag]

/-- The same on a negative finite input, by the sign symmetry. -/
theorem key_fround_finite_neg {m : Nat} (hm : 0 < m) (e : Int) :
    key (froundUnpacked (.finite .negative m e hm)) = -clamp32 (mag32 m e) := by
  rcases narrowed32_cases (round32_narrowed .positive hm e) with hz | ⟨m', e', hp, hr, hmlt, hge, hn⟩
  · have hzn : UnpackedFloat.round .binary32 .negative m e = .zero .negative := by
      rw [round32_neg, hz]; rfl
    rw [fround_of_zero hzn]
    have hz0 : mag32 m e = 0 := by simp only [mag32, hz, key]
    have hpz := int_two_pow_pos 1202
    simp only [key, clamp32, hz0]
    rw [if_neg (by omega : ¬ ((2 : Int) ^ 1202 ≤ 0))]
    simp
  · have hrn : UnpackedFloat.round .binary32 .negative m e = .finite .negative m' e' hp := by
      rw [round32_neg, hr]; rfl
    rw [fround_of_finite hrn]
    have hpos := key_fround_finite_pos hm e
    rw [fround_of_finite hr] at hpos
    by_cases hbig : (105 : Int) ≤ e'
    · rw [if_pos hbig] at hpos ⊢
      simp only [key, Sign.apply] at hpos ⊢
      omega
    · rw [if_neg hbig] at hpos ⊢
      rw [key_round_negF .binary64 52 (by decide) hp e', hpos]

/-! ## The narrowing is monotone -/

theorem fround_infinity (s : Sign) : froundUnpacked (.infinity s) = .infinity s := rfl

theorem fround_zero (s : Sign) : froundUnpacked (.zero s) = .zero s := rfl

theorem key_zero (s : Sign) : key (.zero s) = 0 := rfl

theorem key_finite (s : Sign) (m : Nat) (e : Int) (h : 0 < m) :
    key (.finite s m e h) = s.apply ((m : Int) * 2 ^ (e + 1074).toNat) := rfl

theorem key_inf_pos : key (.infinity .positive) = HUGE := rfl

theorem key_inf_neg : key (.infinity .negative) = -HUGE := rfl

theorem key_fround_zero (s : Sign) : key (froundUnpacked (.zero s)) = 0 := rfl

theorem finite_mag_pos {m : Nat} (hm : 0 < m) (e : Int) :
    0 < (m : Int) * 2 ^ (e + 1074).toNat :=
  Int.mul_pos (by omega) (int_two_pow_pos _)

theorem key_fround_finite_nonneg {m : Nat} {e : Int} (hm : 0 < m) :
    0 ≤ key (froundUnpacked (.finite .positive m e hm)) := by
  rw [key_fround_finite_pos hm e]
  exact clamp32_nonneg (mag32_nonneg hm e)

theorem key_fround_finite_nonpos {m : Nat} {e : Int} (hm : 0 < m) :
    key (froundUnpacked (.finite .negative m e hm)) ≤ 0 := by
  rw [key_fround_finite_neg hm e]
  have := clamp32_nonneg (mag32_nonneg hm e)
  omega

theorem key_fround_bounds {w : UnpackedFloat} (hw : Canonical w) (hn : w ≠ .notANumber) :
    -HUGE ≤ key (froundUnpacked w) ∧ key (froundUnpacked w) ≤ HUGE := by
  have hp := HUGE_pos
  cases hw with
  | notANumber => exact absurd rfl hn
  | infinity s =>
    cases s
    · rw [fround_infinity, key_inf_neg]; omega
    · rw [fround_infinity, key_inf_pos]; omega
  | zero s => rw [key_fround_zero]; omega
  | subnormal s m hm hlt =>
    cases s
    · rw [key_fround_finite_neg hm (-1074)]
      have h1 := clamp32_nonneg (mag32_nonneg hm (-1074))
      have h2 := clamp32_le_HUGE (mag32 m (-1074))
      omega
    · rw [key_fround_finite_pos hm (-1074)]
      have h1 := clamp32_nonneg (mag32_nonneg hm (-1074))
      have h2 := clamp32_le_HUGE (mag32 m (-1074))
      omega
  | normal s m e hm hlo hhi helo hehi =>
    cases s
    · rw [key_fround_finite_neg hm e]
      have h1 := clamp32_nonneg (mag32_nonneg hm e)
      have h2 := clamp32_le_HUGE (mag32 m e)
      omega
    · rw [key_fround_finite_pos hm e]
      have h1 := clamp32_nonneg (mag32_nonneg hm e)
      have h2 := clamp32_le_HUGE (mag32 m e)
      omega

/-- Away from NaN and the infinities, a canonical float is a zero or a
finite value that is canonical in its own right. -/
theorem canonical_zero_or_finite {w : UnpackedFloat} (hw : Canonical w) (hn : w ≠ .notANumber)
    (hi : ∀ s, w ≠ .infinity s) :
    (∃ s, w = .zero s) ∨ ∃ (s : Sign) (m : Nat) (e : Int) (hp : 0 < m),
      w = .finite s m e hp ∧ Canonical (.finite s m e hp) := by
  cases hw with
  | notANumber => exact absurd rfl hn
  | infinity s => exact absurd rfl (hi s)
  | zero s => exact Or.inl ⟨s, rfl⟩
  | subnormal s m hm hlt => exact Or.inr ⟨s, m, -1074, hm, rfl, .subnormal s m hm hlt⟩
  | normal s m e hm hlo hhi helo hehi =>
      exact Or.inr ⟨s, m, e, hm, rfl, .normal s m e hm hlo hhi helo hehi⟩

/-- The core: two finite inputs, compared through their keys. -/
theorem key_fround_mono_finite {su sv : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {h₁ : 0 < m₁} {h₂ : 0 < m₂}
    (hc₁ : Canonical (.finite su m₁ e₁ h₁)) (hc₂ : Canonical (.finite sv m₂ e₂ h₂))
    (h : key (.finite su m₁ e₁ h₁) ≤ key (.finite sv m₂ e₂ h₂)) :
    key (froundUnpacked (.finite su m₁ e₁ h₁))
      ≤ key (froundUnpacked (.finite sv m₂ e₂ h₂)) := by
  obtain ⟨_, he₁, _, _⟩ := canonical_finite_bounds hc₁
  obtain ⟨_, he₂, _, _⟩ := canonical_finite_bounds hc₂
  rw [key_finite, key_finite] at h
  have hn₁ := mag32_nonneg h₁ e₁
  have hn₂ := mag32_nonneg h₂ e₂
  have hq₁ := finite_mag_pos h₁ e₁
  have hq₂ := finite_mag_pos h₂ e₂
  cases su <;> cases sv <;> simp only [Sign.apply] at h
  · rw [key_fround_finite_neg h₁ e₁, key_fround_finite_neg h₂ e₂]
    have := clamp32_mono (mag32_mono h₂ h₁ he₂ he₁ (by omega))
    omega
  · rw [key_fround_finite_neg h₁ e₁, key_fround_finite_pos h₂ e₂]
    have hc1 := clamp32_nonneg hn₁
    have hc2 := clamp32_nonneg hn₂
    omega
  · exact absurd h (by omega)
  · rw [key_fround_finite_pos h₁ e₁, key_fround_finite_pos h₂ e₂]
    exact clamp32_mono (mag32_mono h₁ h₂ he₁ he₂ h)

/-- Narrowing to binary32 and back never reverses an order, at the key
layer where the rounding lemmas live. -/
theorem key_froundUnpacked_mono {u v : UnpackedFloat}
    (hu : Canonical u) (hv : Canonical v) (hun : u ≠ .notANumber) (hvn : v ≠ .notANumber)
    (h : key u ≤ key v) :
    key (froundUnpacked u) ≤ key (froundUnpacked v) := by
  have hp := HUGE_pos
  have hbu := key_fround_bounds hu hun
  have hbv := key_fround_bounds hv hvn
  -- An infinity at either extreme settles the comparison by the bounds alone.
  by_cases hui : u = .infinity .negative
  · subst hui
    rw [fround_infinity, key_inf_neg]
    exact hbv.1
  by_cases hvi : v = .infinity .positive
  · subst hvi
    rw [fround_infinity, key_inf_pos]
    exact hbu.2
  -- The other two placements contradict the hypothesis.
  by_cases hui2 : u = .infinity .positive
  · exfalso
    subst hui2
    rw [key_inf_pos] at h
    by_cases hvneg : v = .infinity .negative
    · subst hvneg
      rw [key_inf_neg] at h
      omega
    · have hlt := key_lt_HUGE hv (fun s hs => by cases s; exact hvneg hs; exact hvi hs)
      omega
  by_cases hvi2 : v = .infinity .negative
  · exfalso
    subst hvi2
    rw [key_inf_neg] at h
    have hlt := key_lt_HUGE hu (fun s hs => by cases s; exact hui hs; exact hui2 hs)
    omega
  -- What is left is zeros and finite values.
  rcases canonical_zero_or_finite hu hun
      (fun s hs => by cases s; exact hui hs; exact hui2 hs) with
    ⟨su, rfl⟩ | ⟨su, m₁, e₁, hp₁, rfl, hc₁⟩ <;>
  rcases canonical_zero_or_finite hv hvn
      (fun s hs => by cases s; exact hvi2 hs; exact hvi hs) with
    ⟨sv, rfl⟩ | ⟨sv, m₂, e₂, hp₂, rfl, hc₂⟩
  · rw [key_fround_zero, key_fround_zero]
    omega
  · rw [key_fround_zero, key_zero, key_finite] at *
    cases sv
    · exact absurd h (by simp only [Sign.apply]; have := finite_mag_pos hp₂ e₂; omega)
    · exact key_fround_finite_nonneg hp₂
  · rw [key_fround_zero, key_zero, key_finite] at *
    cases su
    · exact key_fround_finite_nonpos hp₁
    · exact absurd h (by simp only [Sign.apply]; have := finite_mag_pos hp₁ e₁; omega)
  · exact key_fround_mono_finite hc₁ hc₂ h

/-! ## Crossing back to `Float` -/

/-- The narrowing's output is a shape the binary64 pack understands, and
never a NaN. -/
theorem fround_finite_shape {s : Sign} {m : Nat} {e : Int} (hm : 0 < m) :
    RoundShape (froundUnpacked (.finite s m e hm))
      ∧ froundUnpacked (.finite s m e hm) ≠ .notANumber := by
  rcases narrowed32_cases (round32_narrowed s hm e) with hz | ⟨m', e', hp, hr, hmlt, hge, hn⟩
  · rw [fround_of_zero hz]
    exact ⟨.canonical (.zero s), fun hc => UnpackedFloat.noConfusion hc⟩
  · rw [fround_of_finite hr]
    by_cases hbig : (105 : Int) ≤ e'
    · rw [if_pos hbig]
      exact ⟨.canonical (.infinity s), fun hc => UnpackedFloat.noConfusion hc⟩
    · rw [if_neg hbig]
      have hlog : m'.log2 < 24 := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp hp)).mpr hmlt
      have hcap : totalExponent m' e' ≤ 3900 := by
        simp only [totalExponent]
        omega
      exact round_shape s hp e' hcap

theorem froundUnpacked_shape {w : UnpackedFloat} (hw : Canonical w) (hn : w ≠ .notANumber) :
    RoundShape (froundUnpacked w) ∧ froundUnpacked w ≠ .notANumber := by
  cases hw with
  | notANumber => exact absurd rfl hn
  | infinity s =>
    rw [fround_infinity]
    exact ⟨.canonical (.infinity s), fun hc => UnpackedFloat.noConfusion hc⟩
  | zero s =>
    rw [fround_zero]
    exact ⟨.canonical (.zero s), fun hc => UnpackedFloat.noConfusion hc⟩
  | subnormal s m hm hlt => exact fround_finite_shape hm
  | normal s m e hm hlo hhi helo hehi => exact fround_finite_shape hm

theorem unpack_tsFround (x : Float) :
    (tsFround x).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64 (froundUnpacked x.toModel.unpack)) := rfl

/-- Narrowing to binary32 and back never reverses an order. Every other
order fact about `Math.fround` is this one instantiated. -/
theorem tsFround_mono {x y : Float} (h : Float.le x y = true) :
    Float.le (tsFround x) (tsFround y) = true := by
  rw [float_le_unpack] at h
  have hcx : Canonical x.toModel.unpack := canonical_unpack _
  have hcy : Canonical y.toModel.unpack := canonical_unpack _
  have hxn := le_ne_nan_left h
  have hyn := le_ne_nan_right h
  have hkey := key_froundUnpacked_mono hcx hcy hxn hyn (key_of_le hcx hcy h)
  obtain ⟨hsx, hnx⟩ := froundUnpacked_shape hcx hxn
  obtain ⟨hsy, hny⟩ := froundUnpacked_shape hcy hyn
  rw [float_le_unpack, unpack_tsFround, unpack_tsFround]
  exact le_of_key (canonical_unpack _) (canonical_unpack _)
    (unpack_pack_ne_nan hsx hnx) (unpack_pack_ne_nan hsy hny)
    (key_unpack_pack_mono hsx hsy hnx hny hkey)

/-! ## The shapes a residual carries

`c` is the claim's own constant, so `tsFround c` is ground and grind
evaluates it during preprocessing. A fact separating the hypothesis
constant from the goal's bound cannot be keyed at all: grind refuses a
pattern whose parameter occurs only in hypotheses. -/

theorem tsFround_le_of_le_const {x c : Float} (h : Float.le x c = true)
    (hc : Float.le (tsFround c) c = true) : Float.le (tsFround x) c = true :=
  FloatFacts.float_le_trans (tsFround_mono h) hc

theorem tsFround_ge_of_ge_const {x c : Float} (h : Float.le c x = true)
    (hc : Float.le c (tsFround c) = true) : Float.le c (tsFround x) = true :=
  FloatFacts.float_le_trans hc (tsFround_mono h)

/-- A finite input inside binary32's range narrows to a finite value.
There is no unconditional propagation: a finite binary64 value beyond
that range overflows to an infinity. -/
theorem tsFround_hi_of_le {x c : Float} (h : Float.le x c = true)
    (hc : tsFround c < floatInf) : tsFround x < floatInf :=
  FloatFacts.float_lt_of_le_of_lt (tsFround_mono h) hc

theorem tsFround_lo_of_ge {x c : Float} (h : Float.le c x = true)
    (hc : -floatInf < tsFround c) : -floatInf < tsFround x :=
  FloatFacts.float_lt_of_lt_of_le hc (tsFround_mono h)

end Js.Number.FroundFacts
