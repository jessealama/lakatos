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
