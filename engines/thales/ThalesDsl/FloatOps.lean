import Init.Data.Float.Model.Float

/-!
Binary64 operations JavaScript has and Lean does not.

Lean ships no float remainder at all — no `Float.mod`, no `Mod Float`
instance — so `%` has nothing to map to. It is built here from
`Float.Model` rather than an `extern`, which keeps it reducible in the
kernel: the `decide` rung can evaluate it, and no proof that uses it
rests on an axiom.
-/

namespace ThalesDsl.FloatOps

open Float.Model Float.Model.UnpackedFloat

/-- The remainder of two finite, nonzero floats. Aligning both mantissas
to the smaller exponent makes the pair exact integers, so the truncated
`Int` remainder — which already takes the dividend's sign, as JavaScript
does — is the exact answer; `normalize` only repacks it. -/
def remFinite (spec : Format) (s₁ : Sign) (m₁ : Nat) (e₁ : Int)
    (s₂ : Sign) (m₂ : Nat) (e₂ : Int) : UnpackedFloat :=
  let e := min e₁ e₂
  let a : Int := s₁.apply (m₁ <<< (e₁ - e).toNat)
  let b : Int := s₂.apply (m₂ <<< (e₂ - e).toNat)
  -- A zero remainder keeps the dividend's sign: `-6 % 3` is `-0`.
  normalize spec (a.tmod b) e s₁

/-- `Number::remainder`: NaN whenever the dividend is infinite or the
divisor is zero, and the dividend unchanged when only the divisor is
infinite. -/
def remUnpacked (spec : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity _, _ => .notANumber
  | _, .zero _ => .notANumber
  | .zero s, _ => .zero s
  | .finite s m e h, .infinity _ => .finite s m e h
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ => remFinite spec s₁ m₁ e₁ s₂ m₂ e₂

/-- The model of JavaScript's `%`. This is C `fmod`, not the IEEE
`remainder` operation: the quotient is truncated, not rounded to nearest.
The result is exact in every case — `remFinite` says why — but that
argument is carried by the bit-exact tests, not yet by a proof. -/
def tsRem (a b : Float) : Float :=
  .ofModel (.pack (remUnpacked Format.binary64 a.toModel.unpack b.toModel.unpack))

end ThalesDsl.FloatOps
