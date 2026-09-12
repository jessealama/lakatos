import Js

open Js.Number.FloatFacts Float.Model Float.Model.UnpackedFloat

/-! The generic rounding core must agree with the binary64 theory
definitionally, so every existing proof keeps working, and must
instantiate at binary32. -/

example (m : Nat) (e : Int) : gridF .binary64 m e = grid m e := rfl
example (m : Nat) (e : Int) : WellPlacedF .binary64 m e = WellPlaced m e := rfl
example : Format.binary64.mantissaBits = 52 + 1 := by decide
example : Format.binary32.mantissaBits = 23 + 1 := by decide
example : (-1074 : Int) ≤ Format.binary32.minExponent := by decide

-- Binary32 satisfies every side condition the generic theorems ask for.
example (m : Nat) (e : Int) (num den : Nat) (hw : WellPlacedF .binary32 m e)
    (hden : 0 < den) (hnum : num < den) :
    key (roundWithAccuracy .binary32 .positive m e (accuracyOfFraction num den)) =
      rnShiftF m ((gridF .binary32 m e - e).toNat) num den
        * 2 ^ (gridF .binary32 m e + 1074).toNat :=
  key_roundWA_posF .binary32 23 (by decide) (by decide) m e num den hw hden hnum

-- Binary32 rounding is monotone on values, which is what the narrowing needs.
example {m₁ m₂ : Nat} {E₁ E₂ : Int} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (h : m₁ * 2 ^ (E₁ - min E₁ E₂).toNat ≤ m₂ * 2 ^ (E₂ - min E₁ E₂).toNat) :
    key (UnpackedFloat.round .binary32 .positive m₁ E₁)
      ≤ key (UnpackedFloat.round .binary32 .positive m₂ E₂) :=
  key_round32_pos_mono h₁ h₂ h
