import Js.Number.Basic
import Init.Data.Float.Model.Float

/-!
Binary64 operations JavaScript has and Lean does not: `%`, the integral
roundings Lean ships only as opaque externs, the sign unit, and the
ordered minimum and maximum.

Lean ships no float remainder at all — no `Float.mod`, no `Mod Float`
instance — so `%` has nothing to map to. It is built here from
`Float.Model` rather than an `extern`, which keeps it reducible in the
kernel: `decide` can evaluate it, and no proof that uses it rests on an
axiom.

There is likewise no `Float.min` or `Float.max`: only the order-derived
generic `min`/`max`, which disagree with ECMA-262 on both a NaN operand
and the ordering of the two zeros, and disagree differently depending on
which argument comes first. So those are built here too.
-/

namespace Js.Number.FloatOps

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

/-- The integral neighbour a fractional magnitude rounds to. -/
inductive RoundDir where
  | towardZero | towardNegInf | towardPosInf | nearestHalfUp

/-- Round to an integral value in the given direction. A finite value
with a non-negative exponent is already integral; otherwise the mantissa
loses its fraction bits, and floor/ceil bump the magnitude when the
dropped bits were nonzero and the sign matches the direction. `normalize`
repacks; its `zeroSign` carries the input's sign, so a magnitude that
rounds to zero keeps it (`Math.ceil(-0.5)` is `-0`).

`nearestHalfUp` compares the dropped bits against half of their place
value rather than testing them for zero, which is what keeps it exact:
`Math.round` is not `Math.floor(x + 0.5)`, since that sum rounds before
the floor does. Ties go toward `+∞`, so the positive side bumps on a
half and the negative side does not. The match names every direction:
a new one must state its own rule rather than inherit a catch-all. -/
def roundIntegral (spec : Format) (dir : RoundDir) : UnpackedFloat → UnpackedFloat
  | .notANumber => .notANumber
  | .infinity s => .infinity s
  | .zero s => .zero s
  | .finite s m e h =>
    if e ≥ 0 then .finite s m e h
    else
      let k := (-e).toNat
      let q := m >>> k
      let frac := m % 2 ^ k
      let inexact := frac != 0
      -- `e < 0` here, so `k ≥ 1` and the half below is a place value.
      let half := 2 ^ (k - 1)
      let bump :=
        match dir, s with
        | .towardZero, _ => false
        | .towardNegInf, .negative => inexact
        | .towardNegInf, .positive => false
        | .towardPosInf, .positive => inexact
        | .towardPosInf, .negative => false
        | .nearestHalfUp, .positive => decide (half ≤ frac)
        | .nearestHalfUp, .negative => decide (half < frac)
      normalize spec (s.apply (if bump then q + 1 else q)) 0 s

/-- `Math.trunc`: toward zero. -/
def tsTrunc (a : Float) : Float :=
  .ofModel (.pack (roundIntegral Format.binary64 .towardZero a.toModel.unpack))

/-- `Math.floor`: toward negative infinity. -/
def tsFloor (a : Float) : Float :=
  .ofModel (.pack (roundIntegral Format.binary64 .towardNegInf a.toModel.unpack))

/-- `Math.ceil`: toward positive infinity. -/
def tsCeil (a : Float) : Float :=
  .ofModel (.pack (roundIntegral Format.binary64 .towardPosInf a.toModel.unpack))

/-- `Math.round`: to nearest, ties toward positive infinity. -/
def tsRound (a : Float) : Float :=
  .ofModel (.pack (roundIntegral Format.binary64 .nearestHalfUp a.toModel.unpack))

/-- `Math.sign`: the unit of the input's sign. NaN and the zeros come back
unchanged — `Math.sign(-0)` is `-0` — and every other value, subnormals
and infinities included, is `±1`. -/
def tsSign (a : Float) : Float :=
  match a.toModel.unpack with
  | .notANumber => a
  | .zero _ => a
  | .infinity .negative => -1.0
  | .infinity .positive => 1.0
  | .finite .negative _ _ _ => -1.0
  | .finite .positive _ _ _ => 1.0

/-! `Math.min` and `Math.max` are binary here; the emitter folds a call
site's arguments over them, and the identities `+∞` and `-∞` cover the
empty call. `Float`'s own `<` is the numeric order and reduces in the
kernel, so it decides every pair but two: a NaN operand, against which
every comparison is false, and two zeros, which compare equal yet must
still be ordered. Both are read off the unpacked view. Every other
numerically-equal pair is bit-identical, so which one comes back does not
matter. -/

/-- `Math.min`: a NaN operand makes the result NaN — C `fmin` drops it —
and `-0` is below `+0`. -/
def tsMin (a b : Float) : Float :=
  match a.toModel.unpack, b.toModel.unpack with
  | .notANumber, _ => floatNaN
  | _, .notANumber => floatNaN
  | .zero .negative, .zero _ => a
  | .zero _, .zero .negative => b
  | _, _ => if a < b then a else b

/-- `Math.max`: the mirror of `tsMin`. NaN still propagates, and the
preferred zero is `+0`. -/
def tsMax (a b : Float) : Float :=
  match a.toModel.unpack, b.toModel.unpack with
  | .notANumber, _ => floatNaN
  | _, .notANumber => floatNaN
  | .zero .positive, .zero _ => a
  | .zero _, .zero .positive => b
  | _, _ => if a < b then b else a

/-- `Number::sameValue`, the meaning of `Object.is` on numbers.
Propositional equality on `Float` is exactly SameValue — every NaN is
one value, the zeros are two; `SameValueTest.lean` pins that
correspondence on both evaluation paths — so the model is its `Bool`
face. -/
def sameValue (x y : Float) : Bool := decide (x = y)

end Js.Number.FloatOps
