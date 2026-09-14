import Js.Binders
import Js.Number.Decimal

/-!
StringToNumber (7.1.4.1.1) and the two global parsers, `parseFloat` (19.2.4)
and `parseInt` (19.2.5).

All three read the numeric-literal grammar and hand the digits they collect
to `Decimal.ofScientific`, which is core's own decimal-to-binary conversion.
So `Number("0.1")` and the literal `0.1` are the same term by construction
rather than by agreement of two roundings, and an exponent big enough to
overflow — `"1e99999999999999999999"` — is a `Nat` that conversion's own
guards dispose of rather than something to overflow here. A mantissa is the
exact integer its digits spell, so a forty-digit string is converted once and
correctly rounded rather than approximated at twenty digits.

The sign is never part of what is converted: it is applied afterwards with
`Decimal.withSign`, so `"-0"`, `"-0e5"`, and `"-1e-400"` are all `-0`.
-/

namespace Js.Number

open Float.Model.UnpackedFloat (Sign)

/-! ## White space -/

/-- The code points `StrWhiteSpaceChar` accepts: TAB, LF, VT, FF, CR, SP,
NBSP (U+00A0), ZWNBSP (U+FEFF), the rest of Unicode's `Zs` (U+1680,
U+2000–U+200A, U+202F, U+205F, U+3000), and the two remaining line
terminators (U+2028, U+2029) — twenty-four in all.

U+180E, MONGOLIAN VOWEL SEPARATOR, is **not** one: it left `Zs` in Unicode
6.3, and test262's `*_U180E.js` tests pin that it is not skipped. -/
def isStrWhiteSpace (c : Char) : Bool :=
  let n := c.toNat
  n == 0x09 || n == 0x0A || n == 0x0B || n == 0x0C || n == 0x0D || n == 0x20 ||
    n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) ||
    n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000 ||
    n == 0xFEFF

/-- Drop the leading white space of a character list. -/
def trimStartChars : List Char → List Char
  | [] => []
  | c :: rest => if isStrWhiteSpace c then trimStartChars rest else c :: rest

/-- Drop the white space at both ends of a character list. -/
def trimChars (l : List Char) : List Char :=
  (trimStartChars (trimStartChars l).reverse).reverse

/-! ## Digits -/

/-- A character's value as a radix-36 digit: `0`–`9`, then `a`–`z` and
`A`–`Z` for 10–35. Nothing else is a digit, so U+0661 ARABIC-INDIC DIGIT ONE
is not one and `Number("١")` is NaN. -/
def digitValue (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n && n ≤ 0x7A then some (n - 0x61 + 10)
  else if 0x41 ≤ n && n ≤ 0x5A then some (n - 0x41 + 10)
  else none

/-- The longest prefix of digits below `base`: its exact value, how many
there were, and what is left. -/
def digitsPrefixAux (base acc count : Nat) : List Char → Nat × Nat × List Char
  | [] => (acc, count, [])
  | c :: rest =>
    match digitValue c with
    | some d => if d < base then digitsPrefixAux base (acc * base + d) (count + 1) rest
                else (acc, count, c :: rest)
    | none => (acc, count, c :: rest)

/-- The longest prefix of digits below `base`, from the start. -/
def digitsPrefix (base : Nat) (l : List Char) : Nat × Nat × List Char :=
  digitsPrefixAux base 0 0 l

/-! ## The numeric-literal grammar -/

/-- An optional leading sign, and what follows it. -/
def signPrefix : List Char → Sign × List Char
  | '+' :: rest => (.positive, rest)
  | '-' :: rest => (.negative, rest)
  | l => (.positive, l)

/-- `ExponentPart`, and only a complete one: `e` or `E`, an optional sign,
and at least one digit. `1e` and `1e+` leave the `e` unconsumed, which is
what makes `Number("1e")` NaN and `parseFloat("1e")` `1`. -/
def exponentPart? : List Char → Option (Int × List Char)
  | c :: rest =>
    if c == 'e' || c == 'E' then
      let (s, rest') := signPrefix rest
      let (v, n, rest'') := digitsPrefix 10 rest'
      if n = 0 then none
      else some (match s with | .negative => -(v : Int) | .positive => (v : Int), rest'')
    else none
  | [] => none

/-- The longest `StrUnsignedDecimalLiteral` prefix that is not `Infinity`, as
a mantissa, a decimal exponent, and the rest: `DecimalDigits [. DecimalDigits]
[ExponentPart]` or `. DecimalDigits [ExponentPart]`. The mantissa is every
digit on both sides of the point read as one exact `Nat`, and the exponent is
the `ExponentPart`'s value less the number of fraction digits. There are no
numeric separators in this grammar, so `1_0` stops at the `_`. -/
def unsignedDecimal? (l : List Char) : Option (Nat × Int × List Char) :=
  let (whole, nw, r₁) := digitsPrefix 10 l
  match r₁ with
  | '.' :: r₂ =>
    let (frac, nf, r₃) := digitsPrefix 10 r₂
    if nw = 0 ∧ nf = 0 then none
    else
      let m := whole * 10 ^ nf + frac
      match exponentPart? r₃ with
      | some (e, r₄) => some (m, e - nf, r₄)
      | none => some (m, -(nf : Int), r₃)
  | _ =>
    if nw = 0 then none
    else
      match exponentPart? r₁ with
      | some (e, r₂) => some (whole, e, r₂)
      | none => some (whole, 0, r₁)

/-- The literal `Infinity`, and what follows it. -/
def infinity? : List Char → Option (List Char)
  | 'I' :: 'n' :: 'f' :: 'i' :: 'n' :: 'i' :: 't' :: 'y' :: rest => some rest
  | _ => none

/-- The signed part of StringToNumber: `StrNumericLiteral` without the
non-decimal forms, which have no sign of their own. -/
def signedDecimal (l : List Char) : Float :=
  let (s, rest) := signPrefix l
  match infinity? rest with
  | some r => if r.isEmpty then Decimal.withSign s floatInf else floatNaN
  | none =>
    match unsignedDecimal? rest with
    | some (m, e, r) =>
      if r.isEmpty then Decimal.withSign s (Decimal.ofScientific m e) else floatNaN
    | none => floatNaN

/-- StringToNumber, 7.1.4.1.1: the meaning of `Number(s)` and of a string in
any numeric context. White space at both ends is dropped and an empty string
is `+0`; `0b`, `0o`, and `0x` (either case) take a non-empty run of digits in
that base and nothing else, and carry no sign of their own, so `-0x10` and
`+0x10` are NaN; otherwise an optional sign is followed by `Infinity` or by a
`StrUnsignedDecimalLiteral` that must consume the whole rest. Anything else
is NaN. -/
def stringToNumber (s : String) : Float :=
  match trimChars s.toList with
  | [] => 0.0
  | '0' :: p :: rest =>
    let base? : Option Nat :=
      if p == 'b' || p == 'B' then some 2
      else if p == 'o' || p == 'O' then some 8
      else if p == 'x' || p == 'X' then some 16
      else none
    match base? with
    | some base =>
      let (v, n, r) := digitsPrefix base rest
      if n = 0 ∨ !r.isEmpty then floatNaN else Decimal.ofScientific v 0
    | none => signedDecimal ('0' :: p :: rest)
  | l => signedDecimal l

/-- `parseFloat`, 19.2.4: white space at the **start** only, then a sign,
then `Infinity` or the longest `StrUnsignedDecimalLiteral` prefix, whatever
follows it. NaN when neither matches, so `"."`, `"-"`, and `"e1"` are NaN
while `"0x10"` is `0` — the `0` is a decimal literal and the `x` is trailing
garbage. -/
def parseFloat (s : String) : Float :=
  let (sign, rest) := signPrefix (trimStartChars s.toList)
  match infinity? rest with
  | some _ => Decimal.withSign sign floatInf
  | none =>
    match unsignedDecimal? rest with
    | some (m, e, _) => Decimal.withSign sign (Decimal.ofScientific m e)
    | none => floatNaN

/-- `parseInt`, 19.2.5, with `radix` already put through ToInt32 by the
caller. White space at the start, then a sign; a radix of `0` means 10 and
strips a `0x` prefix, a radix of 16 strips one too, and a radix outside 2–36
is NaN. `Z` is the longest run of radix-`R` digits and an empty one is NaN.
The integer is exact — there is no twenty-digit approximation — so
`parseInt("9007199254740993")` rounds once, in `Decimal.ofScientific`. -/
def parseInt (s : String) (radix : Int) : Float :=
  let (sign, rest) := signPrefix (trimStartChars s.toList)
  if radix ≠ 0 ∧ (radix < 2 ∨ radix > 36) then floatNaN
  else
    let base : Nat := if radix = 0 then 10 else radix.toNat
    let (r, body) :=
      if radix = 0 ∨ radix = 16 then
        match rest with
        | '0' :: c :: tail => if c == 'x' || c == 'X' then (16, tail) else (base, rest)
        | _ => (base, rest)
      else (base, rest)
    let (v, n, _) := digitsPrefix r body
    if n = 0 then floatNaN else Decimal.withSign sign (Decimal.ofScientific v 0)

end Js.Number
