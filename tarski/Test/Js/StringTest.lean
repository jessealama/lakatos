import Js.String.Ops

/-! `JsString`, the UTF-16 code-unit string, and the total functions the
evaluator's `String` surface dispatches onto.

The point of the representation is that **a surrogate pair comes apart**:
a Lean `Char` is a Unicode scalar value, so `"😀"[0]`,
`String.fromCharCode(0xD800)`, and `"😀".split("")` have no answer in a
Lean `String` at all. The first section below is that claim, stated as
kernel-checked facts — `decide` reduces a `JsString` literal, which is
why `List UInt16` was chosen over `Array UInt16`.

The second claim is the defect `tarski/test262/failures.md` filed against
#391: the relational order is **code-unit** order, under which
`"\u{10000}"` is less than `"￿"`, where Lean's `String` order —
code points — says the opposite.

Every other case is one `#guard` per `Js/String/Ops.lean` function at its
edges. `Test/Tarski/StringBuiltinsTest.lean` is the other side: the same
operations reached through the evaluator, with their coercions and their
refusals. -/

open Js JsString

private def S (s : String) : JsString := ofString s

/-! ## The representation -/

#guard (S "").units == []
#guard (S "abc").units == [97, 98, 99]
#guard (S "é").units == [0xE9]
#guard (S "😀").units == [0xD83D, 0xDE00]
#guard (S "😀").length == 2
#guard (S "abc").length == 3

#guard asString? (S "😀") == some "😀"
#guard asString? ⟨[0xD800]⟩ == none
#guard toStringLossy ⟨[0xD800]⟩ == "�"
#guard toKey (S "ab") == "ab"

/-! ## The surrogate pair comes apart

This is the issue's acceptance criterion. The pair joins under `++`, each
half is a string of its own, and `codePointAt` reads the pair at 0 and
the lone low surrogate at 1. -/

example : (⟨[0xD83D]⟩ : JsString) ++ ⟨[0xDE00]⟩ = S "😀" := by decide

#guard (S "😀").unitAt? 0 == some ⟨[0xD83D]⟩
#guard (S "😀").unitAt? 1 == some ⟨[0xDE00]⟩
#guard (S "😀").unitAt? 2 == none
#guard (S "😀").codeUnitAt? 0 == some 0xD83D
#guard (S "😀").codePointAt? 0 == some (0x1F600, 2)
#guard (S "😀").codePointAt? 1 == some (0xDE00, 1)
#guard (S "abc").codePointAt? 1 == some (98, 1)
#guard ofCodePoint 0x1F600 == S "😀"
#guard singleton 65 == S "A"

#guard isWellFormed (S "😀")
#guard !isWellFormed ⟨[0xD83D]⟩
#guard toWellFormed ⟨[0xD83D]⟩ == S "�"
#guard toWellFormed (S "😀") == S "😀"

/-! ## Kernel reducibility

A `JsString` literal reduces, which is what lets `decide` close a fact
about one and what `Array UInt16` would have cost. -/

example : (S "ab" ≠ S "ac") := by decide
example : ((S "ab" == S "ab") = true) := by decide

/-! ## Code-unit order

The defect #391 owns. The astral literal is spelled with `Char.ofNat`
because Lean's `\u` escape takes exactly four hex digits. -/

private def astral : String := String.singleton (Char.ofNat 0x10000)

example : decide (S astral < S "￿") = true := by decide
-- Lean's own `String` order says the opposite: it is code points.
example : decide (astral < "￿") = false := by decide

#guard decide (S "abc" < S "abd")
#guard decide (S "ab" < S "abc")
#guard !decide (S "abc" < S "abc")

/-! ## Searching -/

#guard indexOf (S "abcabc") (S "bc") 0 == some 1
#guard indexOf (S "abcabc") (S "bc") 2 == some 4
#guard indexOf (S "abc") (S "z") 0 == none
-- An empty pattern is found at the position asked for, clamped.
#guard indexOf (S "abc") (S "") 9 == some 3
#guard indexOf (S "abc") (S "") 1 == some 1
#guard lastIndexOf (S "abcabc") (S "bc") 6 == some 4
#guard lastIndexOf (S "abcabc") (S "bc") 3 == some 1
#guard lastIndexOf (S "abc") (S "") 3 == some 3
#guard includes (S "abc") (S "b") 0
#guard !includes (S "abc") (S "b") 2
#guard startsWith (S "abc") (S "b") 1
#guard endsWith (S "abc") (S "bc") 3
#guard !endsWith (S "abc") (S "bc") 2

/-! ## Indices -/

#guard relativeIndex 3 (some (-1)) false == 2
#guard relativeIndex 3 (some (-9)) false == 0
#guard relativeIndex 3 (some 9) false == 3
#guard relativeIndex 3 none true == 0
#guard relativeIndex 3 none false == 3
#guard clampIndex 3 (some (-1)) true == 0
#guard substring (S "abcde") 3 1 == S "bc"
#guard slice (S "abcde") 1 4 == S "bcd"
#guard slice (S "abcde") 4 1 == S ""

/-! ## Padding and repetition -/

#guard padStart (S "x") 3 (S "ab") == S "abx"
#guard padEnd (S "x") 3 (S "ab") == S "xab"
-- An empty filler leaves the string alone, and so does a `maxLength`
-- the string already reaches.
#guard padStart (S "x") 3 (S "") == S "x"
#guard padStart (S "abc") 2 (S "-") == S "abc"
#guard (S "ab").repeatUnits 0 == S ""
#guard (S "ab").repeatUnits 3 == S "ababab"

/-! ## Splitting -/

#guard (splitOn (S "a,b,,c") (S ",") 4).map toStringLossy == ["a", "b", "", "c"]
#guard (splitOn (S "a,b,,c") (S ",") 3).map toStringLossy == ["a", "b", ""]
#guard (splitOn (S "abc") (S "") 10).map toStringLossy == ["a", "b", "c"]
#guard (splitOn (S "abc") (S "abcd") 10).map toStringLossy == ["abc"]
#guard splitOn (S "abc") (S ",") 0 == []
#guard (splitOn (S "abc") (S ",") 1).map toStringLossy == ["abc"]
-- An empty separator splits a pair into its two code units.
#guard (splitOn (S "😀") (S "") 10).map JsString.units == [[0xD83D], [0xDE00]]

/-! ## Trimming

The table is WhiteSpace ∪ LineTerminator. **U+180E is not in it** — it
left `Zs` in Unicode 6.3, and `trim/u180e.js` checks that it stands. -/

#guard trim (S "﻿　 a ") == S "a"
#guard trim (S "᠎a᠎") == S "᠎a᠎"
#guard trimStart (S " a ") == S "a "
#guard trimEnd (S " a ") == S " a"

/-! ## Case, ASCII only

The limit is the absence of a Unicode character database; #518 owns
it. -/

#guard upperAscii (S "aé") == S "Aé"
#guard lowerAscii (S "AÉ") == S "aÉ"

/-! ## Normalization: the form is validated, the string is not changed -/

#guard normalizeForm? (S "a") (S "NFC") == some (S "a")
#guard normalizeForm? (S "a") (S "NFKD") == some (S "a")
#guard normalizeForm? (S "a") (S "nfc") == none

/-! ## Replacement

GetSubstitution with no captures: `$$`, `$&`, `` $` ``, and `$'` are
substituted and `$1` and `$<a>` stand for themselves. -/

#guard getSubstitution (S "b") (S "abc") 1 (S "[$$|$&|$`|$'|$1|$<a>]")
  == S "[$|b|a|c|$1|$<a>]"
#guard getSubstitution (S "b") (S "abc") 1 (S "$") == S "$"
#guard matchPositions (S "ab") (S "") == [0, 1, 2]
#guard matchPositions (S "aaa") (S "aa") == [0]
#guard matchPositions (S "abc") (S "z") == []

/-! ## Comparison and construction -/

#guard localeCompareUnits (S "a") (S "b") == -1.0
#guard localeCompareUnits (S "a") (S "a") == 0.0
#guard localeCompareUnits (S "b") (S "a") == 1.0
#guard fromCharCode [0xD83D, 0xDE00] == S "😀"
#guard fromCodePoints [0x1F600.toFloat] == .ok (S "😀")
#guard fromCodePoints [1114112.0] == .error 1114112.0
#guard fromCodePoints [1.5] == .error 1.5
#guard fromCodePoints [] == .ok (S "")

/-! ## ToUint32 and ToUint16, the two conversions the surface needs -/

#guard Number.FloatOps.tsToUint32 (-1.0) == 4294967295
#guard Number.FloatOps.tsToUint32 (0.0 / 0.0) == 0
#guard Number.FloatOps.tsToUint16 65601.0 == 65
#guard Number.FloatOps.tsToUint16 (-1.0) == 65535
