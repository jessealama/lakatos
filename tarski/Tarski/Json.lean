import Js

/-! JSON as text: 25.5.1's grammar and 25.5.2.3's quoting.

Nothing here touches the heap or runs user code. `JSON.parse` splits in
two — this file turns a text into a tree, and `Tarski/Eval.lean`'s
`jsonToValue` turns that tree into objects the reviver can walk — because
the grammar is the half test262's `JSON/parse` directory actually
examines, and `#guard` can pin it without a realm.

The grammar is JSON's and not JavaScript's, which is why it is written
out rather than borrowed from `Lean.Json`: only the four white-space
characters, no leading zero, no `+` in front, no `.5` or `5.`, no hex, no
`Infinity` or `NaN`, no trailing comma, no trailing text, the eight
string escapes and no others, and a raw code unit below U+0020 inside a
string refused. A number's *matched text* is handed to the library's
StringToNumber, which is the same definition a numeric literal is — the
JSON number grammar being a sublanguage of StrDecimalLiteral — so no
arithmetic is spelled here at all and `-0` parses to the negative zero
`Object.is` can see.

**Lone surrogates are #391's.** A Lean `String` is a sequence of code
points and cannot hold one, so a `\uD800` with no low surrogate after it
becomes U+FFFD here where the specification names a string this domain
has no room for; a surrogate *pair* is combined into its code point, as
the UTF-16 text it stands for would be. `quoteJsonString` therefore never
meets a lone surrogate to escape. The `JSON` tests that turn on the
difference are classified under #391 in `test262/failures.md`. -/

namespace Tarski

open Js

/-- A parsed JSON text. The grammar's six values, and no more: there is
no distinction here between an integer and a fraction, both being
Numbers, and an object's members keep the text's order so that a repeated
key can be resolved the way 25.5.1.1 resolves it — the last one wins. -/
inductive JsonTree where
  | null
  | bool (b : Bool)
  | num (x : Float)
  | str (s : String)
  | arr (items : List JsonTree)
  | obj (members : List (String × JsonTree))
deriving Repr, BEq, Inhabited

/-- Why a text is not JSON. The two kinds are the two messages V8
gives: running out of text, and meeting a character that cannot be
there. -/
inductive JsonErrorKind where
  | unexpectedToken
  | unexpectedEnd
deriving Repr, DecidableEq, Inhabited

/-- A refusal and where in the text it happened, counted in code points
from zero. -/
structure JsonError where
  kind : JsonErrorKind
  position : Nat
deriving Repr, DecidableEq, Inhabited

/-- The `SyntaxError` message `JSON.parse` raises for the refusal. -/
def JsonError.message : JsonError → String
  | { kind := .unexpectedEnd, .. } => "Unexpected end of JSON input"
  | { kind := .unexpectedToken, position := n } =>
    "Unexpected token in JSON at position " ++ Nat.repr n

/-- The four characters JSONWhitespace admits (25.5.1), and no others: a
vertical tab, a form feed, and U+00A0 are all refusals here where the
script grammar accepts them. -/
def isJsonWhitespace (c : Char) : Bool :=
  c.toNat == 9 || c.toNat == 10 || c.toNat == 13 || c.toNat == 32

/-- Skip white space, carrying the position along. -/
def skipJsonWs : List Char → Nat → List Char × Nat
  | c :: rest, pos => if isJsonWhitespace c then skipJsonWs rest (pos + 1) else (c :: rest, pos)
  | [], pos => ([], pos)

/-- A hexadecimal digit's value; `none` for anything else. Upper and
lower case both, as the grammar's HexDigit has them. -/
def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Four hexadecimal digits as a code unit. -/
def hex4? (a b c d : Char) : Option Nat := do
  let a ← hexDigit? a
  let b ← hexDigit? b
  let c ← hexDigit? c
  let d ← hexDigit? d
  pure (((a * 16 + b) * 16 + c) * 16 + d)

/-- Whether a code unit is a leading surrogate. -/
def isLeadingSurrogate (n : Nat) : Bool := 55296 ≤ n && n ≤ 56319

/-- Whether a code unit is a trailing surrogate. -/
def isTrailingSurrogate (n : Nat) : Bool := 56320 ≤ n && n ≤ 57343

/-- A list of UTF-16 code units as the string they stand for: a
surrogate *pair* is the code point it encodes, and a surrogate on its own
becomes U+FFFD, a Lean `String` having no room for one. See the header,
and #391. A code point above U+FFFF arrives whole — a raw character of
the text is never a surrogate — and passes through. -/
def codeUnitsToChars : List Nat → List Char
  | [] => []
  | [n] =>
    (if isLeadingSurrogate n || isTrailingSurrogate n then Char.ofNat 65533
     else Char.ofNat n) :: []
  | hi :: lo :: rest =>
    if isLeadingSurrogate hi && isTrailingSurrogate lo then
      Char.ofNat (65536 + (hi - 55296) * 1024 + (lo - 56320)) :: codeUnitsToChars rest
    else if isLeadingSurrogate hi || isTrailingSurrogate hi then
      Char.ofNat 65533 :: codeUnitsToChars (lo :: rest)
    else Char.ofNat hi :: codeUnitsToChars (lo :: rest)

/-- Scan a string's body, the opening quote already consumed. The
accumulator holds the code units in reverse: an escape names one, and a
character of the text names its own code point. -/
def scanJsonString (cs : List Char) (pos : Nat) (acc : List Nat) :
    Except JsonError (String × List Char × Nat) :=
  match cs with
  | [] => .error { kind := .unexpectedEnd, position := pos }
  | '"' :: rest => .ok (String.ofList (codeUnitsToChars acc.reverse), rest, pos + 1)
  | '\\' :: e :: rest =>
    if e == '"' then scanJsonString rest (pos + 2) (34 :: acc)
    else if e == '\\' then scanJsonString rest (pos + 2) (92 :: acc)
    else if e == '/' then scanJsonString rest (pos + 2) (47 :: acc)
    else if e == 'b' then scanJsonString rest (pos + 2) (8 :: acc)
    else if e == 'f' then scanJsonString rest (pos + 2) (12 :: acc)
    else if e == 'n' then scanJsonString rest (pos + 2) (10 :: acc)
    else if e == 'r' then scanJsonString rest (pos + 2) (13 :: acc)
    else if e == 't' then scanJsonString rest (pos + 2) (9 :: acc)
    else if e == 'u' then
      match rest with
      | a :: b :: c :: d :: rest' =>
        match hex4? a b c d with
        | none => .error { kind := .unexpectedToken, position := pos + 2 }
        | some n => scanJsonString rest' (pos + 6) (n :: acc)
      | _ => .error { kind := .unexpectedEnd, position := pos + 2 }
    else .error { kind := .unexpectedToken, position := pos + 1 }
  | ['\\'] => .error { kind := .unexpectedEnd, position := pos + 1 }
  | c :: rest =>
    -- A raw code unit below U+0020 must be escaped (25.5.1's
    -- JSONStringCharacter).
    if c.toNat < 32 then .error { kind := .unexpectedToken, position := pos }
    else scanJsonString rest (pos + 1) (c.toNat :: acc)
  termination_by cs.length

/-- A run of decimal digits and what follows it. -/
def scanJsonDigits : List Char → List Char → List Char × List Char
  | c :: rest, acc => if c.isDigit then scanJsonDigits rest (c :: acc) else (acc.reverse, c :: rest)
  | [], acc => (acc.reverse, [])

/-- A JSONNumber (25.5.1): an optional minus, an integer part with no
leading zero, an optional fraction of at least one digit, and an optional
exponent of at least one digit. The *matched text* goes to the library's
StringToNumber — the JSON number grammar is a sublanguage of
StrDecimalLiteral, so that is the specification's "MV of the literal,
rounded" and the very definition the literal `0.1` has. -/
def scanJsonNumber (cs : List Char) (pos : Nat) : Except JsonError (Float × List Char × Nat) :=
  let (sign, afterSign, signLen) :=
    match cs with
    | '-' :: rest => (['-'], rest, 1)
    | _ => (([] : List Char), cs, 0)
  match afterSign with
  | [] => .error { kind := .unexpectedEnd, position := pos + signLen }
  | '0' :: rest =>
    match rest with
    | d :: _ =>
      if d.isDigit then .error { kind := .unexpectedToken, position := pos + signLen + 1 }
      else scanJsonFraction (sign ++ ['0']) rest (pos + signLen + 1)
    | [] => scanJsonFraction (sign ++ ['0']) rest (pos + signLen + 1)
  | d :: _ =>
    if d.isDigit then
      let (ds, rest) := scanJsonDigits afterSign []
      scanJsonFraction (sign ++ ds) rest (pos + signLen + ds.length)
    else .error { kind := .unexpectedToken, position := pos + signLen }
where
  /-- The fraction and the exponent, once the integer part is matched. -/
  scanJsonFraction (matched : List Char) (cs : List Char) (pos : Nat) :
      Except JsonError (Float × List Char × Nat) :=
    let (matched, cs, pos) :=
      match cs with
      | '.' :: rest =>
        let (ds, rest') := scanJsonDigits rest []
        if ds.isEmpty then (matched, '.' :: rest, pos)
        else (matched ++ ('.' :: ds), rest', pos + 1 + ds.length)
      | _ => (matched, cs, pos)
    match cs with
    | '.' :: _ => .error { kind := .unexpectedToken, position := pos + 1 }
    | 'e' :: rest => scanJsonExponent (matched ++ ['e']) rest (pos + 1)
    | 'E' :: rest => scanJsonExponent (matched ++ ['e']) rest (pos + 1)
    | _ => .ok (Number.stringToNumber (String.ofList matched), cs, pos)
  /-- The exponent's optional sign and its digits. -/
  scanJsonExponent (matched : List Char) (cs : List Char) (pos : Nat) :
      Except JsonError (Float × List Char × Nat) :=
    let (matched, cs, pos) :=
      match cs with
      | '+' :: rest => (matched, rest, pos + 1)
      | '-' :: rest => (matched ++ ['-'], rest, pos + 1)
      | _ => (matched, cs, pos)
    let (ds, rest) := scanJsonDigits cs []
    if ds.isEmpty then
      match cs with
      | [] => .error { kind := .unexpectedEnd, position := pos }
      | _ => .error { kind := .unexpectedToken, position := pos }
    else .ok (Number.stringToNumber (String.ofList (matched ++ ds)), rest, pos + ds.length)

mutual

/-- One JSONValue. The fuel is the text's length, which bounds the
nesting depth: every level costs at least its own bracket. -/
def parseJsonValue : Nat → List Char → Nat → Except JsonError (JsonTree × List Char × Nat)
  | 0, _, pos => .error { kind := .unexpectedToken, position := pos }
  | fuel + 1, cs₀, pos₀ =>
    let (cs, pos) := skipJsonWs cs₀ pos₀
    match cs with
    | [] => .error { kind := .unexpectedEnd, position := pos }
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest, pos + 4)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.bool true, rest, pos + 4)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.bool false, rest, pos + 5)
    | '"' :: rest =>
      match scanJsonString rest (pos + 1) [] with
      | .ok (s, rest', pos') => .ok (.str s, rest', pos')
      | .error e => .error e
    | '[' :: rest =>
      let (cs₂, pos₂) := skipJsonWs rest (pos + 1)
      match cs₂ with
      | ']' :: rest₂ => .ok (.arr [], rest₂, pos₂ + 1)
      | _ => parseJsonElements fuel cs₂ pos₂ []
    | '{' :: rest =>
      let (cs₂, pos₂) := skipJsonWs rest (pos + 1)
      match cs₂ with
      | '}' :: rest₂ => .ok (.obj [], rest₂, pos₂ + 1)
      | _ => parseJsonMembers fuel cs₂ pos₂ []
    | c :: _ =>
      if c == '-' || c.isDigit then
        match scanJsonNumber cs pos with
        | .ok (x, rest, pos') => .ok (.num x, rest, pos')
        | .error e => .error e
      else .error { kind := .unexpectedToken, position := pos }

/-- An array's elements, the opening bracket consumed and the list known
not to be empty. -/
def parseJsonElements :
    Nat → List Char → Nat → List JsonTree → Except JsonError (JsonTree × List Char × Nat)
  | 0, _, pos, _ => .error { kind := .unexpectedToken, position := pos }
  | fuel + 1, cs, pos, acc =>
    match parseJsonValue fuel cs pos with
    | .error e => .error e
    | .ok (v, rest, pos') =>
      let (cs₂, pos₂) := skipJsonWs rest pos'
      match cs₂ with
      | ',' :: rest₂ => parseJsonElements fuel rest₂ (pos₂ + 1) (v :: acc)
      | ']' :: rest₂ => .ok (.arr (v :: acc).reverse, rest₂, pos₂ + 1)
      | [] => .error { kind := .unexpectedEnd, position := pos₂ }
      | _ => .error { kind := .unexpectedToken, position := pos₂ }

/-- An object's members, the opening brace consumed and the list known
not to be empty. -/
def parseJsonMembers :
    Nat → List Char → Nat → List (String × JsonTree) →
      Except JsonError (JsonTree × List Char × Nat)
  | 0, _, pos, _ => .error { kind := .unexpectedToken, position := pos }
  | fuel + 1, cs₀, pos₀, acc =>
    let (cs, pos) := skipJsonWs cs₀ pos₀
    match cs with
    | [] => .error { kind := .unexpectedEnd, position := pos }
    | '"' :: rest =>
      match scanJsonString rest (pos + 1) [] with
      | .error e => .error e
      | .ok (k, rest', pos') =>
        let (cs₂, pos₂) := skipJsonWs rest' pos'
        match cs₂ with
        | ':' :: rest₂ =>
          match parseJsonValue fuel rest₂ (pos₂ + 1) with
          | .error e => .error e
          | .ok (v, rest₃, pos₃) =>
            let (cs₄, pos₄) := skipJsonWs rest₃ pos₃
            match cs₄ with
            | ',' :: rest₄ => parseJsonMembers fuel rest₄ (pos₄ + 1) ((k, v) :: acc)
            | '}' :: rest₄ => .ok (.obj ((k, v) :: acc).reverse, rest₄, pos₄ + 1)
            | [] => .error { kind := .unexpectedEnd, position := pos₄ }
            | _ => .error { kind := .unexpectedToken, position := pos₄ }
        | [] => .error { kind := .unexpectedEnd, position := pos₂ }
        | _ => .error { kind := .unexpectedToken, position := pos₂ }
    | _ => .error { kind := .unexpectedToken, position := pos }

end

/-- ParseJSON (25.5.1): the whole text, white space and all, or the first
refusal. Trailing text is a refusal, so `JSON.parse("1 2")` throws rather
than answering `1`. -/
def parseJson (text : String) : Except JsonError JsonTree :=
  let cs := text.toList
  match parseJsonValue (cs.length + 1) cs 0 with
  | .error e => .error e
  | .ok (v, rest, pos) =>
    let (rest', pos') := skipJsonWs rest pos
    match rest' with
    | [] => .ok v
    | _ => .error { kind := .unexpectedToken, position := pos' }

/-- One character of a quoted string: QuoteJSONString's table (25.5.2.3),
with every other code point below U+0020 as a four-digit escape in lower
case. -/
def jsonEscape (c : Char) : String :=
  let n := c.toNat
  if n == 34 then "\\\""
  else if n == 92 then "\\\\"
  else if n == 8 then "\\b"
  else if n == 12 then "\\f"
  else if n == 10 then "\\n"
  else if n == 13 then "\\r"
  else if n == 9 then "\\t"
  else if n < 32 then
    let digit (d : Nat) : Char :=
      if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)
    String.ofList ['\\', 'u', '0', '0', digit (n / 16), digit (n % 16)]
  else String.singleton c

/-- QuoteJSONString (25.5.2.3): the text in double quotes with the seven
named escapes and the control characters spelled out. A lone surrogate
cannot arrive — see the header — so there is no arm for one. -/
def quoteJsonString (s : String) : String :=
  "\"" ++ s.toList.foldl (fun acc c => acc ++ jsonEscape c) "" ++ "\""

end Tarski
