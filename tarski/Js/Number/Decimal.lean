import Js.Number.FloatOps

/-!
The exact decimal view of a binary64, shared by the formatters
(`Js/Number/ToString.lean`) and the parser (`Js/Number/StringToNumber.lean`).

Everything here is built from `Float.Model`. `Float.toString` is an opaque
`extern` with no logical model, so a definition resting on it would neither
reduce in the kernel nor support a proof; nothing below mentions it.

Two directions meet in this file.

**Decimal to binary** is core's own `Float.Model.ofScientific`, not a
reimplementation. It is exact-then-round: for `0 ≤ e` one model
multiplication of the exact operands `m <<< 53` at exponent `-53` and
`10 ^ e`, for `e < 0` one model division of `m` by `10 ^ (-e)`, each
rounding once under RoundTiesToEven. That is what every Lean float literal
means and what the JSON decoder gives a number read off the wire, so the
literal `0.1`, `Number("0.1")`, and the bridge's `0.1` are one term by
construction.

**Binary to decimal** is the specification's own definition, executed. A
finite nonzero binary64 is exactly `m · 2^e`, so its magnitude is an exact
rational `num / den` (`ratio`); `shortest` then searches upward for the
fewest significant digits whose rounded value is the input again, which is
6.1.6.1.20 step 5 read literally rather than Ryu, Grisu, or Dragon4. The
round-trip property is the definition's own acceptance test.
-/

namespace Js.Number.Decimal

open Float.Model Float.Model.UnpackedFloat

/-! ## Decimal to binary -/

/-- The Number value of `m × 10^e`, rounded once under RoundTiesToEven:
core's `Float.Model.ofScientific`, which is the slow path of
`Float.ofScientific` and so the meaning of every decimal literal Lean
parses. `Test/Js/DecimalTest.lean` pins that agreement. -/
def ofScientific (m : Nat) (e : Int) : Float :=
  Float.ofModel (Float.Model.ofScientific m e)

/-- Apply a sign to a magnitude. The sign is always the caller's, never
`ofScientific`'s, so `withSign .negative (ofScientific 0 e)` is `-0` and a
decimal literal that underflows keeps the sign it was written with. -/
def withSign (s : Sign) (x : Float) : Float :=
  match s with
  | .negative => -x
  | .positive => x

/-! ## The exact rational view -/

/-- The exact magnitude of a finite nonzero float as a fraction `num / den`:
`m · 2^e` is `m <<< e` over `1` when `e ≥ 0` and `m` over `1 <<< -e`
otherwise. A zero, an infinity, and a NaN have no such view and answer
`none`; the sign is dropped, so a caller carries it itself. -/
def ratio : UnpackedFloat → Option (Nat × Nat)
  | .finite _ m e _ => if e ≥ 0 then some (m <<< e.toNat, 1) else some (m, 1 <<< (-e).toNat)
  | _ => none

/-! ## Decimal digits of a natural -/

/-- The digits of `n` in base `b`, most significant first. The recursion is
structural in `fuel` rather than well-founded in `n`, so the kernel reduces
it, and `n / b` reaches `0` within `n` steps for every `b ≥ 2`; `digitsBase`
passes `n` itself, as `FloatOps.powNat` does. -/
def digitsBaseAux (b : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | _, 0, acc => acc
  | fuel + 1, n, acc => digitsBaseAux b fuel (n / b) (n % b :: acc)

/-- The digits of `n` in base `b`, most significant first; `[0]` for `0`. -/
def digitsBase (b n : Nat) : List Nat :=
  if n = 0 then [0] else digitsBaseAux b n n []

/-- A digit's character in the alphabet `Number::toString` uses: `0`–`9`
then `a`–`z`, so radix 36 reaches `z`. A value of 36 or more is outside
every caller's range and answers `'?'` rather than a code point of its
own. -/
def digitChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d)
  else if d < 36 then Char.ofNat (87 + d)
  else '?'

/-- `n` written in base `b`, `2 ≤ b ≤ 36`. -/
def natToStringBase (b n : Nat) : String :=
  String.ofList ((digitsBase b n).map digitChar)

/-- `n` written in decimal, with no sign and no leading zero. -/
def decimalDigits (n : Nat) : String := natToStringBase 10 n

/-- How many decimal digits `n` is written with; `1` for `0`. -/
def digitCount (n : Nat) : Nat := (digitsBase 10 n).length

/-! ## The decimal exponent -/

/-- The least `j ≥ 1` with `num · 10^j ≥ den`, searched upward from `lo`.
Only reached with a `lo` the caller has shown is no larger than the answer,
so the fuel arm is unreachable and answers `lo`. -/
def leastScaleAux (num den : Nat) : Nat → Nat → Nat
  | 0, lo => lo
  | fuel + 1, lo => if num * 10 ^ lo ≥ den then lo else leastScaleAux num den fuel (lo + 1)

/-- The `n` with `10^(n-1) ≤ num/den < 10^n` — the decimal exponent of the
exact rational `num/den`, and the `n` of 6.1.6.1.20 step 5 once the digit
count is known.

For `num ≥ den` the value is at least one and `⌊num/den⌋`'s digit count is
the answer. For `num < den` it is `1 - j` for the least `j ≥ 1` with
`num · 10^j ≥ den`, and `j` is found from an estimate rather than by
counting: with `D := den.log2 - num.log2` the true ratio lies strictly
between `2^(D-1)` and `2^(D+1)`, so `⌈log₁₀(den/num)⌉` lies within
`[⌊D·log₁₀2⌋, ⌊D·log₁₀2⌋ + 2]`. `1233/4096` is `log₁₀2` from below, close
enough that over the ~1100 bits a binary64 can span it moves the floor by
less than one, so the estimate is a lower bound and three more comparisons
reach the answer. `num = 0` has no decimal exponent and answers `0`. -/
def decimalExponent (num den : Nat) : Int :=
  if num = 0 then 0
  else if num ≥ den then (digitCount (num / den) : Int)
  else
    let est := ((den.log2 - num.log2) * 1233) / 4096
    let j := leastScaleAux num den 4 (max 1 est)
    1 - (j : Int)

/-! ## Scaling -/

/-- `(num/den) · 10^p` as a fraction, exactly. -/
def scaled (num den : Nat) (p : Int) : Nat × Nat :=
  if p ≥ 0 then (num * 10 ^ p.toNat, den) else (num, den * 10 ^ (-p).toNat)

/-- `⌊(num/den) · 10^p⌋`. -/
def floorScaled (num den : Nat) (p : Int) : Nat :=
  let (a, b) := scaled num den p
  a / b

/-- The integer nearest `(num/den) · 10^p`, a tie going **up** — the
specification's "if there are two such `n`, pick the larger `n`", which
`toFixed`, `toExponential`, and `toPrecision` all name. -/
def roundHalfUpScaled (num den : Nat) (p : Int) : Nat :=
  let (a, b) := scaled num den p
  a / b + (if 2 * (a % b) ≥ b then 1 else 0)

/-! ## The shortest round-tripping digits -/

/-- One level of 6.1.6.1.20 step 5: given the exact magnitude `num/den` of
`x` and its decimal exponent `n`, look for a `k`-digit `s` with
`𝔽(s × 10^(n-k)) = x`, and fall through to `k + 1` when neither candidate
round-trips.

`q := ⌊x · 10^(k-n)⌋` lies in `[10^(k-1), 10^k)`, so `q` and `q + 1` are the
only `k`-digit candidates that can be nearest; a candidate is accepted when
the model's decimal-to-binary conversion gives `x` back, which is the
round-trip property as an executable test rather than as a theorem about a
cleverer algorithm. When both round-trip the note's tie rule applies: the
one closer to `x` — `2r` against `den` — and on an exact tie the even one.
`q + 1 = 10^k` is `k + 1` digits, and is returned as `(1, n + 1)`; that is
the arm `9.999999999999999e22` and `1e23` take, both printing `1e+23`. -/
def shortestFrom (x : Float) (num den : Nat) (n : Int) : Nat → Nat → Nat × Int
  | 0, k => (floorScaled num den ((k : Int) - n), n)
  | fuel + 1, k =>
    let (a, b) := scaled num den ((k : Int) - n)
    let q := a / b
    let r := a % b
    let pick (c : Nat) : Nat × Int := if c = 10 ^ k then (1, n + 1) else (c, n)
    let acceptLow := ofScientific q (n - k) == x
    let acceptHigh := ofScientific (q + 1) (n - k) == x
    if acceptLow && acceptHigh then
      if 2 * r < b then pick q
      else if b < 2 * r then pick (q + 1)
      else if q % 2 == 0 then pick q else pick (q + 1)
    else if acceptLow then pick q
    else if acceptHigh then pick (q + 1)
    else shortestFrom x num den n fuel (k + 1)

/-- The `(s, n)` of 6.1.6.1.20 step 5 for the magnitude of a finite nonzero
`x`: `s` the shortest digit string that reads back as `|x|`, `n` its decimal
exponent, so `|x| = 𝔽(s × 10^(n-k))` with `k` the digit count of `s`. `none`
for a NaN, an infinity, and both zeros, which the formatters answer before
they get here.

Every binary64 round-trips in 17 significant digits, so the search starts at
`k = 1` with fuel 17 and the fuel arm is unreachable. No candidate can carry
a trailing zero: one that did would be a candidate of the level below, and
would have been accepted there. -/
def shortest (x : Float) : Option (Nat × Int) :=
  match ratio x.toModel.unpack with
  | none => none
  | some (num, den) => some (shortestFrom (Float.abs x) num den (decimalExponent num den) 17 1)

end Js.Number.Decimal
