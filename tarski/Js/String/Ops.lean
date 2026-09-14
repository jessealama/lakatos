import Js.String.Basic
import Js.Number.FloatOps

/-! What `String.prototype`'s methods *mean*, as total functions on
`JsString`.

Every arm of the evaluator's `String` surface is dispatch and coercion
over one of these: the order the arguments are coerced in belongs to the
evaluator, and what the method computes belongs here, so a `Theorem`
about a string operation and a run of one appeal to the same definition.
Nothing here throws — a range that cannot be honoured is `none` or a
clamp, and the `TypeError`/`RangeError` is the caller's. Nothing here
runs user code either, which is why `replace` and `replaceAll` are only
half here: `matchPositions` and `getSubstitution` are the meaning, and
the splice around them is the evaluator's, because a replacer may be a
function and a function is `EvalM`.

Two limits are deliberate, and both are the absence of a Unicode
character database rather than a shape this file could not hold:
`upperAscii`/`lowerAscii` map `a`–`z` only, and `normalizeForm?`
validates its form and answers its input. Shipping the UCD is a slice of
its own; the follow-up issue is named in `tarski/test262/failures.md`.
-/

namespace Js
namespace JsString

/-- 6.1.4 lets an implementation cap a String's length anywhere below
2^53 − 1. This is V8's answer, and the only place the cap is observable
is a `repeat` or a `pad` asked for more than it. -/
def maxStringLength : Nat := 1073741824

/-! ### Searching -/

/-- StringIndexOf (6.1.4.1) with the search starting at `start`: the
first index at or after it where `pat` occurs. An empty pattern is found
immediately, which is what makes `"abc".indexOf("", 9)` answer `3`. -/
def indexOf (s pat : JsString) (start : Nat) : Option Nat :=
  ((List.range (s.length + 1)).drop (min start s.length)).find?
    (fun i => pat.units.isPrefixOf (s.units.drop i))

/-- StringLastIndexOf: the greatest index at or before `start` where
`pat` occurs and still fits inside the string. -/
def lastIndexOf (s pat : JsString) (start : Nat) : Option Nat :=
  (List.range (start + 1)).reverse.find?
    (fun i => i + pat.length ≤ s.length && pat.units.isPrefixOf (s.units.drop i))

/-- `String.prototype.includes`, from a position. -/
def includes (s pat : JsString) (start : Nat) : Bool := (indexOf s pat start).isSome

/-- `String.prototype.startsWith`, from a position. -/
def startsWith (s pat : JsString) (start : Nat) : Bool :=
  pat.units.isPrefixOf (s.units.drop start)

/-- `String.prototype.endsWith`, ending at a position. -/
def endsWith (s pat : JsString) (stop : Nat) : Bool :=
  pat.length ≤ stop && stop ≤ s.length && pat.units.isPrefixOf (s.units.drop (stop - pat.length))

/-! ### Indices -/

/-- The clamped absolute index a *relative* argument names — the
`relativeStart`/`relativeEnd` step `slice` and `at` take theirs through.
`i` is ToIntegerOrInfinity's answer, `none` being an infinity whose sign
is `negative`, since the library's `integerOrInfinity?` reports both
infinities the same way. -/
def relativeIndex (len : Nat) (i : Option Int) (negative : Bool) : Nat :=
  match i with
  | none => if negative then 0 else len
  | some n =>
    if n < 0 then (if (len : Int) + n < 0 then 0 else ((len : Int) + n).toNat)
    else if (len : Int) < n then len else n.toNat

/-- The clamped absolute index a *non-relative* argument names — what
`indexOf`, `substring`, `startsWith`, and the pads clamp their position
to, where a negative is 0 rather than an offset from the end. -/
def clampIndex (len : Nat) (i : Option Int) (negative : Bool) : Nat :=
  match i with
  | none => if negative then 0 else len
  | some n => if n < 0 then 0 else if (len : Int) < n then len else n.toNat

/-- `String.prototype.substring`: the two ends clamped and then put in
order, which is the one method that swaps them. -/
def substring (s : JsString) (a b : Nat) : JsString :=
  s.extract (min a b) (max a b)

/-- `String.prototype.slice`: an empty string when the ends cross. -/
def slice (s : JsString) (a b : Nat) : JsString :=
  if a < b then s.extract a b else ⟨[]⟩

/-! ### Padding and repetition -/

/-- StringPad (22.1.3.17.1): the filler repeated and then truncated to
the gap. An empty filler leaves the string alone, and so does a
`maxLength` the string already reaches. -/
def pad (s : JsString) (maxLength : Nat) (fill : JsString) (atStart : Bool) : JsString :=
  if maxLength ≤ s.length || fill.isEmpty then s
  else
    let gap := maxLength - s.length
    let copies := gap / fill.length + 1
    let filler : JsString := ⟨(fill.repeatUnits copies).units.take gap⟩
    if atStart then filler ++ s else s ++ filler

/-- `String.prototype.padStart`. -/
def padStart (s : JsString) (maxLength : Nat) (fill : JsString) : JsString :=
  pad s maxLength fill true

/-- `String.prototype.padEnd`. -/
def padEnd (s : JsString) (maxLength : Nat) (fill : JsString) : JsString :=
  pad s maxLength fill false

/-! ### Splitting -/

/-- `splitOn`'s walk, with the separator's first unit split off so that
it is nonempty by construction and the recursion is visibly
decreasing. -/
def splitGo (s0 : UInt16) (srest cur : List UInt16) : List UInt16 → List (List UInt16)
  | [] => [cur.reverse]
  | u :: rest =>
    if (s0 :: srest).isPrefixOf (u :: rest) then
      cur.reverse :: splitGo s0 srest [] (rest.drop srest.length)
    else splitGo s0 srest (u :: cur) rest
termination_by l => l.length
decreasing_by
  · simp only [List.length_drop, List.length_cons]; omega
  · simp

/-- 22.1.3.23 steps 9–20 with a string separator: `limit` 0 answers
nothing, an empty separator splits into single code units, an empty
string answers itself, and the pieces are the text between successive
non-overlapping occurrences. -/
def splitOn (s sep : JsString) (limit : Nat) : List JsString :=
  if limit = 0 then []
  else
    match sep.units with
    | [] => (s.units.take limit).map (fun u => ⟨[u]⟩)
    | s0 :: srest =>
      if s.units.isEmpty then [s]
      else ((splitGo s0 srest [] s.units).map JsString.mk).take limit

/-! ### Trimming -/

/-- WhiteSpace ∪ LineTerminator as a code-unit table (12.2 and 12.3): the
Unicode `Zs` category at the pin, the five ASCII controls, U+FEFF, and
the two line separators. **U+180E is not here** — it left `Zs` in Unicode
6.3, and test262's `trim/u180e.js` checks that it is not trimmed. -/
def isTrimmable (u : UInt16) : Bool :=
  u == 0x9 || u == 0xA || u == 0xB || u == 0xC || u == 0xD || u == 0x20 ||
    u == 0xA0 || u == 0x1680 || (0x2000 ≤ u && u ≤ 0x200A) ||
    u == 0x2028 || u == 0x2029 || u == 0x202F || u == 0x205F || u == 0x3000 || u == 0xFEFF

/-- `String.prototype.trimStart`. -/
def trimStart (s : JsString) : JsString := ⟨s.units.dropWhile isTrimmable⟩

/-- `String.prototype.trimEnd`. -/
def trimEnd (s : JsString) : JsString := ⟨(s.units.reverse.dropWhile isTrimmable).reverse⟩

/-- `String.prototype.trim`. -/
def trim (s : JsString) : JsString := trimEnd (trimStart s)

/-! ### Case -/

/-- `String.prototype.toUpperCase`, **ASCII only**: Lean has no Unicode
character database, so `"é"` is left alone where an engine answers `"É"`.
The locale forms are this function with their argument ignored. Named
`upperAscii` rather than `toUpperCase` because `scripts/check-boundary.sh`
bans the method syntax `.toU…` under `Tarski/`. -/
def upperAscii (s : JsString) : JsString :=
  ⟨s.units.map (fun u => if 0x61 ≤ u && u ≤ 0x7A then u - 32 else u)⟩

/-- `String.prototype.toLowerCase`, ASCII only for `upperAscii`'s
reason. -/
def lowerAscii (s : JsString) : JsString :=
  ⟨s.units.map (fun u => if 0x41 ≤ u && u ≤ 0x5A then u + 32 else u)⟩

/-- The four forms `String.prototype.normalize` accepts. The
normalization itself is the identity: without the UCD there is no
decomposition to perform, and validating the form is the half of the
method that is observable without it. -/
def normalizeForm? (s form : JsString) : Option JsString :=
  if form = ofString "NFC" || form = ofString "NFD" ||
      form = ofString "NFKC" || form = ofString "NFKD" then some s else none

/-! ### Replacement -/

/-- GetSubstitution (22.1.3.19.1) with no captures and no named groups,
which is every match this slice can produce: `$$`, `$&`, `` $` ``, and
`$'` are substituted and everything else — `$1`, `$<name>`, a trailing
`$` — stands for itself, exactly as it does when `captures` is empty. -/
def substituteGo (matched str : JsString) (position : Nat) :
    List UInt16 → List UInt16
  | [] => []
  | [u] => [u]
  | u :: v :: rest =>
    if u == 0x24 then
      if v == 0x24 then 0x24 :: substituteGo matched str position rest
      else if v == 0x26 then matched.units ++ substituteGo matched str position rest
      else if v == 0x60 then
        (str.units.take position) ++ substituteGo matched str position rest
      else if v == 0x27 then
        (str.units.drop (position + matched.length)) ++ substituteGo matched str position rest
      else u :: substituteGo matched str position (v :: rest)
    else u :: substituteGo matched str position (v :: rest)

/-- GetSubstitution on whole strings. -/
def getSubstitution (matched str : JsString) (position : Nat) (replacement : JsString) :
    JsString :=
  ⟨substituteGo matched str position replacement.units⟩

/-- The positions `String.prototype.replaceAll` matches at: greedy, left
to right, advancing by `max 1 searchLength`, so an empty search matches
between every pair of code units and at both ends. -/
def matchPositions (s search : JsString) : List Nat :=
  let advance := max 1 search.length
  ((List.range (s.length + 1)).foldl
    (fun (acc : List Nat × Nat) i =>
      if acc.2 ≤ i && i + search.length ≤ s.length && search.units.isPrefixOf (s.units.drop i)
      then (acc.1 ++ [i], i + advance) else acc)
    ([], 0)).1

/-! ### Comparison and construction -/

/-- `String.prototype.localeCompare` with no ECMA-402: the code-unit
order, reported as the Number −1, 0, or 1. The three doubles are the
library's, so the evaluator performs no conversion of its own. -/
def localeCompareUnits (a b : JsString) : Float :=
  if a < b then -1.0 else if a = b then 0.0 else 1.0

/-- `String.fromCharCode`: the code units, whatever they are. -/
def fromCharCode (units : List UInt16) : JsString := ⟨units⟩

/-- `String.fromCodePoint`'s fold, answering the first argument that is
not an integral Number in `[0, 0x10FFFF]` so the caller can name it in
its `RangeError`. -/
def fromCodePoints : List Float → Except Float JsString
  | [] => .ok ⟨[]⟩
  | x :: rest =>
    match Number.FloatOps.integerOrInfinity? x with
    | some i =>
      if Number.FloatOps.tsIsInteger x && 0 ≤ i && i ≤ 0x10FFFF then
        match fromCodePoints rest with
        | .ok s => .ok (ofCodePoint i.toNat ++ s)
        | .error e => .error e
      else .error x
    | none => .error x

end JsString
end Js
