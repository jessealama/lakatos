import Js.Number.Decimal

/-!
`Number::toString` and the four `Number.prototype` formatters, each a
transcription of its specification section over the exact decimal view in
`Js/Number/Decimal.lean`. The step numbers are in the doc comments.

Nothing here calls `Float.toString`: core's formatter is an opaque `extern`
with no logical model, it is not ECMA's algorithm, and the issue that asked
for this file forbids it. The digits come from `Decimal.shortest`, which is
6.1.6.1.20 step 5 executed, so the round-trip property these strings have is
the definition's own acceptance test.

Radix 10 is exactly specified and is `toDecimalString`. Every other radix the
specification leaves to the implementation, calling only for "a generalization
of" the decimal algorithm; `toRadixString` is V8's `DoubleToRadixCString`
transcribed over exact rational arithmetic, so what `lakatos exe` prints is
what a user comparing against Node sees.
-/

namespace Js.Number

open Float.Model Float.Model.UnpackedFloat

/-! ## `Number::toString(x, 10)` -/

/-- The magnitude of a positive `x`, 6.1.6.1.20 steps 5–10: the shortest
round-tripping digits `s` and their decimal exponent `n`, then the four
placements — `k ≤ n ≤ 21` digits and `n - k` zeros, `0 < n ≤ 21` a point
after `n` digits, `-6 < n ≤ 0` a leading `0.` and `-n` zeros, and otherwise
`d[.ddd]e±(n-1)`. The exponential arm is only reached with `n > 21` or
`n ≤ -6`, so its exponent is never zero and never prints `e+0`. -/
def decimalMagnitude (x : Float) : String :=
  if x.isInf then "Infinity"
  else
    match Decimal.shortest x with
    | none => "0"
    | some (s, n) =>
      let digits := Decimal.decimalDigits s
      let l := digits.toList
      let k : Int := digits.length
      if k ≤ n ∧ n ≤ 21 then
        digits ++ String.ofList (List.replicate (n - k).toNat '0')
      else if 0 < n ∧ n ≤ 21 then
        String.ofList (l.take n.toNat) ++ "." ++ String.ofList (l.drop n.toNat)
      else if -6 < n ∧ n ≤ 0 then
        "0." ++ String.ofList (List.replicate (-n).toNat '0') ++ digits
      else
        let mantissa :=
          if k = 1 then digits
          else String.ofList (l.take 1) ++ "." ++ String.ofList (l.drop 1)
        mantissa ++ "e" ++ (if n - 1 < 0 then "-" else "+") ++
          Decimal.decimalDigits (n - 1).natAbs

/-- `Number::toString(x, 10)`, 6.1.6.1.20: `NaN`, then `0` for both zeros —
the sign of zero is observable only through `Object.is` and division — then
the sign and the magnitude. This is `String(x)`, `+` with a string operand,
ToPropertyKey, and the binary's own output. -/
def toDecimalString (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x == 0.0 then "0"
  else if Float.lt x 0.0 then "-" ++ decimalMagnitude (-x)
  else decimalMagnitude x

/-! ## `Number::toString(x, radix)` -/

/-- Add one to the last fraction digit of a reversed digit list, dropping
every digit that wraps. `none` is a carry that ran off the front and lands on
the integer part: `(0.99).toString(2)` rounding up to `1`. -/
def bumpReversed (radix : Nat) : List Nat → Option (List Nat)
  | [] => none
  | d :: rest => if d + 1 < radix then some ((d + 1) :: rest) else bumpReversed radix rest

/-- V8's fraction loop over exact arithmetic. `F / D` is what is left of the
value below the point and `delta / D` is half the gap above the original
number, both over the common denominator `D`; each round multiplies both by
the radix, emits `⌊F/D⌋`, and keeps the remainder. The loop stops when what
is left is below half an ulp, or — when the remaining fraction is past the
half-way point and adding the ulp would carry — by rounding the digit just
written up and propagating.

The answer is the reversed digit list and whether the carry reached the
integer part. Fuel 1100: a subnormal's fraction has at most 1074 bits and
`delta` at least doubles every round, so the loop ends well inside that and
the fuel arm is unreachable. -/
def radixFractionAux (radix D : Nat) : Nat → Nat → Nat → List Nat → List Nat × Bool
  | 0, _, _, acc => (acc, false)
  | fuel + 1, frac, delta, acc =>
    let frac' := frac * radix
    let delta' := delta * radix
    let digit := frac' / D
    let rest := frac' % D
    let acc' := digit :: acc
    if (D < 2 * rest ∨ (2 * rest = D ∧ digit % 2 = 1)) ∧ D < rest + delta' then
      match bumpReversed radix acc' with
      | some l => (l, false)
      | none => ([], true)
    else if rest ≥ delta' then radixFractionAux radix D fuel rest delta' acc'
    else (acc', false)

/-- The magnitude of a positive finite `x` in a radix other than 10. The
integer part `⌊x⌋` is exact; the fraction, if it is at least half an ulp, is
`radixFractionAux`'s digits after the point.

`delta` is half the gap above `x`, which for the canonical `m · 2^e` is
`2^(e-1)`, floored at `2^-1074` as V8 floors it at the smallest positive
double. Over the common denominator `2 · den` that is `2^e` when `e ≥ 0`,
`2` at the subnormal exponent, and `1` in between. -/
def radixMagnitude (x : Float) (radix : Nat) : String :=
  if x.isInf then "Infinity"
  else
    match x.toModel.unpack with
    | .finite _ m e _ =>
      let den : Nat := if e ≥ 0 then 1 else 1 <<< (-e).toNat
      let num : Nat := if e ≥ 0 then m <<< e.toNat else m
      let D := 2 * den
      let delta : Nat := if e ≥ 0 then 2 ^ e.toNat else if e ≤ -1074 then 2 else 1
      let integer := num / den
      let frac := 2 * (num % den)
      if frac ≥ delta then
        let (revDigits, carry) := radixFractionAux radix D 1100 frac delta []
        let whole := Decimal.natToStringBase radix (if carry then integer + 1 else integer)
        if revDigits.isEmpty then whole
        else whole ++ "." ++ String.ofList (revDigits.reverse.map Decimal.digitChar)
      else Decimal.natToStringBase radix integer
    | _ => "0"

/-- `Number::toString(x, radix)` for `2 ≤ radix ≤ 36`. Radix 10 is
`toDecimalString`; every other radix is the implementation-defined
generalization described in this module's header. The non-finite values and
both zeros print as they do in decimal. -/
def toRadixString (x : Float) (radix : Nat) : String :=
  if radix = 10 then toDecimalString x
  else if x.isNaN then "NaN"
  else if x == 0.0 then "0"
  else if Float.lt x 0.0 then "-" ++ radixMagnitude (-x) radix
  else radixMagnitude x radix

/-! ## `Number.prototype.toFixed` -/

/-- The magnitude of `Number.prototype.toFixed`, 21.1.3.3 steps 7–10 for a
non-negative finite `x` and `0 ≤ f ≤ 100`: a magnitude at or above `10^21`
falls back to `Number::toString`, and otherwise the digits are the integer
nearest `x · 10^f` — a tie going up — padded on the left to `f + 1` digits
and split by a point `f` digits from the end. -/
def toFixedMagnitude (x : Float) (f : Nat) : String :=
  if Float.le (Decimal.ofScientific 1 21) x then toDecimalString x
  else
    let n :=
      match Decimal.ratio x.toModel.unpack with
      | none => 0
      | some (num, den) => Decimal.roundHalfUpScaled num den f
    let m := Decimal.decimalDigits n
    if f = 0 then m
    else
      let l := List.replicate (f + 1 - m.length) '0' ++ m.toList
      String.ofList (l.take (l.length - f)) ++ "." ++ String.ofList (l.drop (l.length - f))

/-- `Number.prototype.toFixed`, 21.1.3.3 steps 6–10, for a finite `x` and an
`f` the caller has already range-checked. Step 6 compares `x < 0`, which `-0`
fails, so `(-0).toFixed(1)` is `0.0` while `(-0.1).toFixed(0)` is `-0`. -/
def toFixedString (x : Float) (f : Nat) : String :=
  if Float.lt x 0.0 then "-" ++ toFixedMagnitude (-x) f else toFixedMagnitude x f

/-! ## `Number.prototype.toExponential` -/

/-- `m` and `e` joined as `d[.ddd]e±e`, the shape steps 10–12 of
`toExponential` and step 9.c of `toPrecision` share. The exponent is always
signed, and `0` prints as `+0`. -/
def exponentialForm (m : String) (e : Int) : String :=
  let l := m.toList
  let mantissa :=
    if m.length ≤ 1 then m
    else String.ofList (l.take 1) ++ "." ++ String.ofList (l.drop 1)
  mantissa ++ "e" ++ (if e < 0 then "-" else "+") ++ Decimal.decimalDigits e.natAbs

/-- The magnitude of `Number.prototype.toExponential`, 21.1.3.2 steps 8–12
for a non-negative finite `x`. A zero is `f + 1` zeros at exponent `0`.
`none` is an undefined `fractionDigits`, step 9.b: the fewest digits that read
back as `x`, which is `Decimal.shortest`. `some f` is step 9.a: the integer
nearest `x · 10^(f - e)` with `e` the decimal exponent less one, a tie going
up; rounding to `10^(f+1)` is a digit too many and becomes `10^f` one
exponent higher, which is how `(25).toExponential(0)` is `3e+1` and
`(0.9999).toExponential(0)` is `1e+0`. -/
def toExponentialMagnitude (x : Float) (f? : Option Nat) : String :=
  if x == 0.0 then exponentialForm (String.ofList (List.replicate (f?.getD 0 + 1) '0')) 0
  else
    match Decimal.ratio x.toModel.unpack with
    | none => exponentialForm "0" 0
    | some (num, den) =>
      match f? with
      | none =>
        match Decimal.shortest x with
        | none => exponentialForm "0" 0
        | some (s, n) => exponentialForm (Decimal.decimalDigits s) (n - 1)
      | some f =>
        let e := Decimal.decimalExponent num den - 1
        let n := Decimal.roundHalfUpScaled num den ((f : Int) - e)
        if n = 10 ^ (f + 1) then exponentialForm (Decimal.decimalDigits (10 ^ f)) (e + 1)
        else exponentialForm (Decimal.decimalDigits n) e

/-- `Number.prototype.toExponential`, 21.1.3.2 steps 7–12, for a finite `x`
and an `f` the caller has already range-checked. -/
def toExponentialString (x : Float) (f? : Option Nat) : String :=
  if Float.lt x 0.0 then "-" ++ toExponentialMagnitude (-x) f?
  else toExponentialMagnitude x f?

/-! ## `Number.prototype.toPrecision` -/

/-- The magnitude of `Number.prototype.toPrecision`, 21.1.3.5 steps 8–13 for
a non-negative finite `x` and `1 ≤ p ≤ 100`. A zero is `p` zeros at exponent
`0`. Otherwise `n` has exactly `p` digits — the integer nearest
`x · 10^(p-1-e)`, a tie going up, and `10^p` becoming `10^(p-1)` one exponent
higher — and then `e < -6 ∨ e ≥ p` is the exponential form, `e = p - 1` the
digits alone, `e ≥ 0` a point `e + 1` digits in, and the rest a leading `0.`
with `-(e+1)` zeros. -/
def toPrecisionMagnitude (x : Float) (p : Nat) : String :=
  let placed (m : String) (e : Int) : String :=
    if e < -6 ∨ e ≥ (p : Int) then exponentialForm m e
    else if e = (p : Int) - 1 then m
    else if e ≥ 0 then
      String.ofList (m.toList.take (e + 1).toNat) ++ "." ++
        String.ofList (m.toList.drop (e + 1).toNat)
    else "0." ++ String.ofList (List.replicate (-(e + 1)).toNat '0') ++ m
  if x == 0.0 then placed (String.ofList (List.replicate p '0')) 0
  else
    match Decimal.ratio x.toModel.unpack with
    | none => placed "0" 0
    | some (num, den) =>
      let e := Decimal.decimalExponent num den - 1
      let n := Decimal.roundHalfUpScaled num den ((p : Int) - 1 - e)
      if n = 10 ^ p then placed (Decimal.decimalDigits (10 ^ (p - 1))) (e + 1)
      else placed (Decimal.decimalDigits n) e

/-- `Number.prototype.toPrecision`, 21.1.3.5 steps 6–14, for a finite `x` and
a `p` the caller has already range-checked. -/
def toPrecisionString (x : Float) (p : Nat) : String :=
  if Float.lt x 0.0 then "-" ++ toPrecisionMagnitude (-x) p
  else toPrecisionMagnitude x p

end Js.Number
