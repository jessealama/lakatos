import Js.Runtime

/-! What a JS string *is*: 6.1.4's sequence of UTF-16 code units.

A Lean `Char` is a Unicode scalar value, so a Lean `String` cannot hold a
lone surrogate at all — `"\uD800"`, `String.fromCharCode(0xD800)`,
`"😀"[0]`, `"😀".split("")`, and `"😀".slice(0, 1)` have no representable
answer in one. The String type is what `length`, indexing, `charCodeAt`,
`codePointAt`, and the relational order are *defined over*, so the
evaluator's strings are the code units themselves.

`List UInt16` rather than `Array UInt16` because the kernel reduces a
list: `decide` closes a fact about a literal string, and `simp` can carry
one through a reduction. The evaluator's strings are test-sized, so the
representation's cost is not the constraint the choice is made under.

`Coe String JsString` is what keeps `.str "abc"` and `.strLit "abc"`
spellable: a Lean string literal elaborates as the code units it names.
The conversion back is two functions rather than one, because it is not
total — `asString?` answers `none` at a lone surrogate, and
`toStringLossy` substitutes U+FFFD, which is what a UTF-8 stdout does
too.

Nothing here is UTF-8: `String.length` and `String.toList` appear only in
`ofString`, where a `Char` is a code point on its way to being encoded.
-/

namespace Js

/-- A JS String value: a sequence of UTF-16 code units (6.1.4). A lone
surrogate is a value like any other. -/
structure JsString where
  units : List UInt16
deriving DecidableEq, Hashable, Inhabited

namespace JsString

/-- A leading (high) surrogate code unit. -/
def isHighSurrogate (u : UInt16) : Bool := 0xD800 ≤ u && u ≤ 0xDBFF

/-- A trailing (low) surrogate code unit. -/
def isLowSurrogate (u : UInt16) : Bool := 0xDC00 ≤ u && u ≤ 0xDFFF

/-- Either half of a surrogate pair. -/
def isSurrogate (u : UInt16) : Bool := 0xD800 ≤ u && u ≤ 0xDFFF

/-- UTF16EncodeCodePoint (11.1.1): a code point below the first
supplementary plane is one unit, anything above it is the pair. -/
def encodeCodePoint (cp : Nat) : List UInt16 :=
  if cp < 0x10000 then [UInt16.ofNat cp]
  else
    let v := cp - 0x10000
    [UInt16.ofNat (0xD800 + v / 0x400), UInt16.ofNat (0xDC00 + v % 0x400)]

/-- The code units a Lean `String` names. Every `Char` is a scalar value,
so no lone surrogate can arise here; the other direction is where the
difference between the two types lives. -/
def ofString (s : String) : JsString :=
  ⟨s.toList.flatMap (fun c => encodeCodePoint c.toNat)⟩

instance : Coe String JsString := ⟨ofString⟩

/-- U+FFFD, what an unpaired surrogate prints as. -/
def replacementChar : Char := Char.ofNat 0xFFFD

/-- The scalar values a unit sequence names, an unpaired surrogate
becoming U+FFFD. This is decoding *for display*: `asString?` is the
question of whether anything was lost. -/
def toChars : List UInt16 → List Char
  | [] => []
  | [u] => [if isSurrogate u then replacementChar else Char.ofNat u.toNat]
  | h :: l :: rest =>
    if isHighSurrogate h && isLowSurrogate l then
      Char.ofNat (0x10000 + (h.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00)) :: toChars rest
    else if isSurrogate h then replacementChar :: toChars (l :: rest)
    else Char.ofNat h.toNat :: toChars (l :: rest)

/-- IsStringWellFormedUnicode (11.1.4 and 22.1.3.9): no unpaired
surrogate. -/
def isWellFormedUnits : List UInt16 → Bool
  | [] => true
  | [u] => !isSurrogate u
  | h :: l :: rest =>
    if isHighSurrogate h && isLowSurrogate l then isWellFormedUnits rest
    else if isSurrogate h then false
    else isWellFormedUnits (l :: rest)

/-- `String.prototype.isWellFormed`. -/
def isWellFormed (s : JsString) : Bool := isWellFormedUnits s.units

/-- `String.prototype.toWellFormed`: every unpaired surrogate replaced by
U+FFFD, the pairs left alone. -/
def toWellFormedUnits : List UInt16 → List UInt16
  | [] => []
  | [u] => if isSurrogate u then [0xFFFD] else [u]
  | h :: l :: rest =>
    if isHighSurrogate h && isLowSurrogate l then h :: l :: toWellFormedUnits rest
    else if isSurrogate h then 0xFFFD :: toWellFormedUnits (l :: rest)
    else h :: toWellFormedUnits (l :: rest)

/-- `String.prototype.toWellFormed`. -/
def toWellFormed (s : JsString) : JsString := ⟨toWellFormedUnits s.units⟩

/-- The Lean `String` this names, or `none` when a lone surrogate makes
the question unanswerable. Named `asString?` rather than `toString?`
because `scripts/check-boundary.sh` bans the method syntax `.toString`
under `Tarski/`. -/
def asString? (s : JsString) : Option String :=
  if isWellFormedUnits s.units then some (String.ofList (toChars s.units)) else none

/-- The Lean `String` a printer gets: each unpaired surrogate is U+FFFD,
which is what Node writes to a UTF-8 stream too. -/
def toStringLossy (s : JsString) : String := String.ofList (toChars s.units)

/-- A property key is a Lean `String` (`Tarski/Value.lean`'s heap), so
this is the one place the two representations meet, and it is lossy: a
lone-surrogate key and a U+FFFD key are one key. No test in the slice
exercises a lone-surrogate *property key*; the collision is filed as a
follow-up rather than paid for with a `JsString`-keyed heap. -/
def toKey (s : JsString) : String := s.toStringLossy

/-- The number of code units — `String.prototype.length`. -/
def length (s : JsString) : Nat := s.units.length

/-- Whether the string is `""`. -/
def isEmpty (s : JsString) : Bool := s.units.isEmpty

instance : Append JsString := ⟨fun a b => ⟨a.units ++ b.units⟩⟩

/-- Concatenating two literals is the literal of their concatenation.
This is what keeps a reduction's string terms *folded*: `simp` never has
to open `ofString` on a literal, so `String.reduceAppend` closes a
template's or a `+`'s walk exactly as it did when a string was a Lean
`String`. -/
@[simp] theorem ofString_append (a b : String) :
    ofString a ++ ofString b = ofString (a ++ b) := by
  show JsString.mk _ = JsString.mk _
  simp only [ofString, String.toList_append, List.flatMap_append]

instance : EmptyCollection JsString := ⟨⟨[]⟩⟩

/-- The one-unit string at an index, or `none` past the end — a String
exotic object's own index property. -/
def unitAt? (s : JsString) (i : Nat) : Option JsString :=
  s.units[i]?.map (fun u => ⟨[u]⟩)

/-- The code unit at an index — `charCodeAt`. -/
def codeUnitAt? (s : JsString) (i : Nat) : Option UInt16 := s.units[i]?

/-- The one-unit string a code unit names. -/
def singleton (u : UInt16) : JsString := ⟨[u]⟩

/-- The string a code point names — `String.fromCodePoint`'s per-argument
step. -/
def ofCodePoint (cp : Nat) : JsString := ⟨encodeCodePoint cp⟩

/-- CodePointAt (11.1.4): the code point starting at an index and the
number of units it took. An unpaired surrogate answers itself, one unit
long, which is what `codePointAt` reports. -/
def codePointAt? (s : JsString) (i : Nat) : Option (Nat × Nat) :=
  match s.units[i]? with
  | none => none
  | some u =>
    if isHighSurrogate u then
      match s.units[i + 1]? with
      | some l =>
        if isLowSurrogate l then
          some (0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00), 2)
        else some (u.toNat, 1)
      | none => some (u.toNat, 1)
    else some (u.toNat, 1)

/-- The units from `start` up to but not including `stop`, both already
clamped by the caller. -/
def extract (s : JsString) (start stop : Nat) : JsString :=
  ⟨(s.units.drop start).take (stop - start)⟩

/-- `n` copies, end to end. -/
def repeatUnits (s : JsString) : Nat → JsString
  | 0 => ⟨[]⟩
  | n + 1 => s ++ repeatUnits s n

/-- The pieces joined by a separator — what `Array.prototype.join` and
`String.prototype.split`'s inverse both mean. -/
def intercalate (sep : JsString) : List JsString → JsString
  | [] => ⟨[]⟩
  | [x] => x
  | x :: rest => x ++ sep ++ intercalate sep rest

/-- IsLessThan step 3: **code-unit** order, not code-point order. This is
the whole difference the representation exists for — `"\u{10000}"` is
less than `"￿"` in JavaScript, and greater in Lean's `String`
order. -/
instance : LT JsString := ⟨fun a b => a.units < b.units⟩

instance (a b : JsString) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.units < b.units))

instance : LE JsString := ⟨fun a b => ¬ b < a⟩

instance (a b : JsString) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable ¬ (b.units < a.units))

/-- Printed as the Lean string literal it names when it names one, and as
its units when it does not, so a `repr`-comparing test keeps its
spelling and a lone surrogate is still readable. -/
instance : Repr JsString where
  reprPrec s prec :=
    match s.asString? with
    | some str => reprPrec str prec
    | none => Repr.addAppParen ("JsString.mk " ++ repr s.units) prec

end JsString

end Js
