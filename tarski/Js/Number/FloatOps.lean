import Js.Number.Basic
import Js.Number.Constants
import Init.Data.Float.Model.Float

/-!
Binary64 operations JavaScript has and Lean does not: `%`, the integral
roundings Lean ships only as opaque externs, the sign unit, the ordered
minimum and maximum, and the binary32 narrowing behind `Math.fround`.

Lean ships no float remainder at all — no `Float.mod`, no `Mod Float`
instance — so `%` has nothing to map to. It is built here from
`Float.Model` rather than an `extern`, which keeps it reducible in the
kernel: `decide` can evaluate it, and no proof that uses it rests on an
axiom.

There is likewise no `Float.min` or `Float.max`: only the order-derived
generic `min`/`max`, which disagree with ECMA-262 on both a NaN operand
and the ordering of the two zeros, and disagree differently depending on
which argument comes first. So those are built here too.

Core has `Float.toFloat32` and `Float32.toFloat`, but both are `opaque`
with no logical model, so a model built on them would not reduce in the
kernel. `Math.fround` is built from `Float.Model` instead, at the
`binary32` format the model already carries.
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

/-- Narrow a finite value to binary32 and widen it back. `round` at
binary32 never overflows: it caps the exponent but leaves the result
finite, and only packing turns a too-large exponent into an infinity.
Packing at binary32 biases by `127 + 23` against a 255 ceiling, so an
exponent of 105 or more is overflow and nothing else. Below that the
survivor carries at most 24 significant bits, which binary64 rounds
exactly; that second rounding is what restores binary64 canonical form
for the final pack. Underflow to a binary32 subnormal or a zero of the
input's sign falls out of `round`'s exponent capping. -/
def froundUnpacked : UnpackedFloat → UnpackedFloat
  | .notANumber => .notANumber
  | .infinity s => .infinity s
  | .zero s => .zero s
  | .finite s m e _ =>
    match round Format.binary32 s m e with
    | .finite s' m' e' _ =>
      if 105 ≤ e' then .infinity s' else round Format.binary64 s' m' e'
    | narrowed => narrowed

/-- `Math.fround`: to binary32 with roundTiesToEven and back. -/
def tsFround (a : Float) : Float :=
  .ofModel (.pack (froundUnpacked a.toModel.unpack))

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

/-- `IsIntegralNumber`, which `Number.isInteger` returns directly: finite,
and equal to its own truncation. The comparison is the IEEE one, matching
the spec's comparison of real numbers rather than SameValue — `ℝ(-0)` is
`0`, so both zeros are integral and `Number.isInteger(-0)` is `true`. -/
def tsIsInteger (a : Float) : Bool :=
  a.isFinite && Float.beq (tsTrunc a) a

/-- `Number.isSafeInteger`: integral, and inside the safe magnitude. The
spec bounds `abs(ℝ(x))`, so the two signs share one comparison. -/
def tsIsSafeInteger (a : Float) : Bool :=
  tsIsInteger a && Float.le (Float.abs a) Number.MAX_SAFE_INTEGER

/-- `Number::sameValue`, the meaning of `Object.is` on numbers.
Propositional equality on `Float` is exactly SameValue — every NaN is
one value, the zeros are two; `SameValueTest.lean` pins that
correspondence on both evaluation paths — so the model is its `Bool`
face. -/
def sameValue (x y : Float) : Bool := decide (x = y)


/-! ## The core operations under `Js.` names

`Math.abs`, `Math.sqrt`, `Number.isFinite`, and `Number.isNaN` are
exactly specified, and core's own operations _are_ the model:
`Init.Data.Float.Model.Float` gives `abs`, `sqrt`, `isFinite`, and
`isNaN` a logical model, so `decide` closes claims about them and
nothing written here would improve on them. The emitter names them as
`Float.*` directly, which `Test/Js/FloatBuiltinsTest.lean` pins. These
aliases exist so the evaluator — whose boundary check
(`scripts/check-boundary.sh`) forbids every `Float.` spelling under
`Tarski/` — can name the same terms through the library, which is the
sanctioned route. Being `abbrev`s they _are_ the same terms, so a later
correspondence proof sees one definition rather than two.
-/

/-- `Math.abs`: core's `Float.abs` under a `Js.` name. -/
abbrev tsAbs : Float → Float := Float.abs

/-- `Math.sqrt`: core's `Float.sqrt` under a `Js.` name. -/
abbrev tsSqrt : Float → Float := Float.sqrt

/-- `Number.isFinite`'s numeric core: core's `Float.isFinite` under a
`Js.` name. -/
abbrev tsIsFinite : Float → Bool := Float.isFinite

/-- `Number.isNaN`'s numeric core: core's `Float.isNaN` under a `Js.`
name. -/
abbrev tsIsNaN : Float → Bool := Float.isNaN

/-! ## Exponentiation

`Number::exponentiate` is the meaning of both `**` and `Math.pow`. Its
special-case table is exact, and is transcribed below in the
specification's own order. Its last step — a finite nonzero base raised
to a finite nonzero exponent — the specification leaves
*implementation-approximated*, and repeated squaring over Lean's own `*`
is one such approximation: exact whenever the true power is
representable (`2 ** 53`, `2 ** -52`, `10 ** 22`), and correctly rounded
nowhere in general.

A **non-integral** exponent has no answer here at all. This library is
built from `Float.Model` and never from an `extern`, core's `Float.pow`,
`Float.exp`, and `Float.log` carry no model, and a transcendental model
is its own piece of work (GitHub #434). So that case answers `floatNaN`,
the same kind of honest placeholder as `Tarski.Format.formatNumber` on a
value needing an exponent: `Test/Js/FloatPowTest.lean` pins
`tsPow 4.0 0.5` as a limit rather than as the truth.
-/

/-- The magnitude of an integral finite value, as a `Nat`: the mantissa
shifted by the exponent, the sign dropped. Anything else — a zero, an
infinity, a NaN, or a finite value with a fraction — answers `0`, so a
caller must have established integrality first. -/
def natOfIntegral : UnpackedFloat → Nat
  | .finite _ m e _ => if e ≥ 0 then m <<< e.toNat else m >>> (-e).toNat
  | _ => 0

/-- `b ^ n` by repeated squaring: `b ^ n = (b * b) ^ (n / 2)`, times `b`
again when `n` is odd. The recursion is structural in `fuel` rather than
well-founded in `n`, so the kernel reduces it; `powNat` passes `n`
itself, and `n / 2` reaches `0` within `log₂ n + 1 ≤ n` steps. Every
multiplication rounds, which is the approximation the section header
describes. -/
def powNatAux (b : Float) : Nat → Nat → Float
  | _, 0 => 1.0
  | 0, _ => 1.0
  | fuel + 1, n =>
    let half := powNatAux (b * b) fuel (n / 2)
    if n % 2 == 0 then half else b * half

/-- `b ^ n` for a natural exponent. -/
def powNat (b : Float) (n : Nat) : Float := powNatAux b n n

/-- Whether a value is an odd integral Number, which is what decides the
sign of an infinite or a zero base raised to a power. -/
def isOddInteger (e : Float) : Bool :=
  tsIsInteger e && Float.abs (tsRem e 2.0) == 1.0

/-- `Number::exponentiate`: `**` and `Math.pow` are this one definition.
The arms are the specification's table in its order — the exponent's NaN
and zeros first, then the base's NaN, infinities, and zeros, then an
infinite exponent against `abs(base)` versus 1, then finite against
finite.

In that last arm an integral exponent is `powNat` of its magnitude,
divided into 1 when it is negative. A non-integral exponent is
`floatNaN`: for a negative base that is the specification's own answer,
and for a positive base it is the placeholder the section header
describes (#434). -/
def tsPow (base exponent : Float) : Float :=
  match base.toModel.unpack, exponent.toModel.unpack with
  | _, .notANumber => floatNaN
  | _, .zero _ => 1.0
  | .notANumber, _ => floatNaN
  -- Neither NaN nor zero, so the exponent's own sign decides.
  | .infinity .positive, _ => if exponent > 0.0 then floatInf else 0.0
  | .infinity .negative, _ =>
    if exponent > 0.0 then (if isOddInteger exponent then -floatInf else floatInf)
    else if isOddInteger exponent then -0.0 else 0.0
  | .zero .positive, _ => if exponent > 0.0 then 0.0 else floatInf
  | .zero .negative, _ =>
    if exponent > 0.0 then (if isOddInteger exponent then -0.0 else 0.0)
    else if isOddInteger exponent then -floatInf else floatInf
  | .finite .., .infinity expSign =>
    let magnitude := Float.abs base
    if magnitude == 1.0 then floatNaN
    else
      match expSign with
      | .positive => if magnitude > 1.0 then floatInf else 0.0
      | .negative => if magnitude > 1.0 then 0.0 else floatInf
  | .finite .., unpackedExponent@(.finite ..) =>
    if !tsIsInteger exponent then floatNaN
    else
      let magnitude := powNat base (natOfIntegral unpackedExponent)
      if exponent < 0.0 then 1.0 / magnitude else magnitude

end Js.Number.FloatOps
