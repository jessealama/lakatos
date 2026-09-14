import Tarski.Json

/-! `Tarski/Json.lean`'s grammar, with no heap in sight.

25.5.1's grammar is JSON's and not JavaScript's, and the difference is
what test262's `JSON/parse` directory examines: which characters count as
white space, whether a leading zero is a number, which escapes a string
admits, and where a refusal is reported. All of that is a pure function
of a text, so all of it is a `#guard` here rather than a program run;
`Test/Tarski/JsonTest.lean` is the half that needs a realm.

A number's *matched text* goes to the library's StringToNumber, so `0.1`
here and the literal `0.1` in a script are the same double and `-0`
parses to the negative zero `Object.is` can see. -/

open Tarski

/-- A parse that succeeded, or `none`. -/
private def parsed (text : String) : Option JsonTree :=
  match parseJson text with
  | .ok t => some t
  | .error _ => none

/-- A parse that failed, as the message `JSON.parse` would raise. -/
private def refusal (text : String) : String :=
  match parseJson text with
  | .ok _ => "<accepted>"
  | .error e => e.message

/-! ## White space is the four characters and no others -/

#guard parsed " 1" == some (.num 1.0)
#guard parsed "\t1" == some (.num 1.0)
#guard parsed "\n1" == some (.num 1.0)
#guard parsed "\r1" == some (.num 1.0)
#guard parsed " \t\n\r 1 \t\n\r " == some (.num 1.0)

-- A vertical tab and a form feed are white space to the *script*
-- grammar and not to this one.
#guard refusal (String.ofList [Char.ofNat 11, '1']) == "Unexpected token in JSON at position 0"
#guard refusal (String.ofList [Char.ofNat 12, '1']) == "Unexpected token in JSON at position 0"
#guard refusal (String.ofList [Char.ofNat 160, '1']) == "Unexpected token in JSON at position 0"

/-! ## Numbers -/

#guard parsed "0" == some (.num 0.0)
#guard parsed "-0" == some (.num (-0.0))
-- `-0` is the *negative* zero, which is what `Object.is` sees and what
-- `JSON.stringify` then prints as `0`.
#guard match parsed "-0" with
  | some (.num x) => Js.JsVal.sameValue (.num x) (.num (-0.0))
  | _ => false
#guard parsed "0.1" == some (.num 0.1)
#guard parsed "1E-2" == some (.num 0.01)
#guard parsed "1e2" == some (.num 100.0)
#guard parsed "1e+2" == some (.num 100.0)
#guard parsed "-1.5e-1" == some (.num (-0.15))
#guard parsed "1e400" == some (.num Js.Number.POSITIVE_INFINITY)

-- No leading zero, no leading `+`, no bare `.5` or `5.`, no hex, and
-- neither of the two non-finite spellings the script grammar has.
#guard refusal "01" == "Unexpected token in JSON at position 1"
#guard refusal "+1" == "Unexpected token in JSON at position 0"
#guard refusal ".5" == "Unexpected token in JSON at position 0"
#guard refusal "5." == "Unexpected token in JSON at position 2"
#guard refusal "0x1" == "Unexpected token in JSON at position 1"
#guard refusal "Infinity" == "Unexpected token in JSON at position 0"
#guard refusal "NaN" == "Unexpected token in JSON at position 0"
#guard refusal "1e" == "Unexpected end of JSON input"
#guard refusal "-" == "Unexpected end of JSON input"

/-! ## Strings -/

#guard parsed "\"\"" == some (.str "")
#guard parsed "\"abc\"" == some (.str "abc")
#guard parsed "\"\\\"\"" == some (.str "\"")
#guard parsed "\"\\\\\"" == some (.str "\\")
#guard parsed "\"\\/\"" == some (.str "/")
#guard parsed "\"\\b\"" == some (.str (String.ofList [Char.ofNat 8]))
#guard parsed "\"\\f\"" == some (.str (String.ofList [Char.ofNat 12]))
#guard parsed "\"\\n\"" == some (.str "\n")
#guard parsed "\"\\r\"" == some (.str "\r")
#guard parsed "\"\\t\"" == some (.str "\t")
#guard parsed "\"\\u0041\"" == some (.str "A")
-- A surrogate pair is the code point it encodes; a lone surrogate has
-- no code point a Lean `String` can hold, and U+FFFD stands in (#391).
#guard parsed "\"\\ud834\\udd1e\"" == some (.str (String.ofList [Char.ofNat 119070]))
#guard parsed "\"\\ud800\"" == some (.str (String.ofList [Char.ofNat 65533]))

#guard refusal "\"a" == "Unexpected end of JSON input"
#guard refusal "\"\t\"" == "Unexpected token in JSON at position 1"
#guard refusal "\"\\x\"" == "Unexpected token in JSON at position 2"
#guard refusal "\"\\u00g0\"" == "Unexpected token in JSON at position 3"

/-! ## Arrays, objects, and what is not one -/

#guard parsed "[]" == some (.arr [])
#guard parsed "{}" == some (.obj [])
#guard parsed "[1,[2,{\"b\":null}],true,false]"
  == some (.arr [.num 1.0, .arr [.num 2.0, .obj [("b", .null)]], .bool true, .bool false])
#guard parsed "{ \"a\" : 1 , \"b\" : [ ] }" == some (.obj [("a", .num 1.0), ("b", .arr [])])

-- A repeated key keeps both members here; 25.5.1.1 resolves them by
-- defining each in turn, so the last one wins where it matters.
#guard parsed "{\"a\":1,\"a\":2}" == some (.obj [("a", .num 1.0), ("a", .num 2.0)])

#guard refusal "" == "Unexpected end of JSON input"
#guard refusal "[1,]" == "Unexpected token in JSON at position 3"
#guard refusal "{\"a\":1,}" == "Unexpected token in JSON at position 7"
#guard refusal "[1" == "Unexpected end of JSON input"
#guard refusal "{\"a\"}" == "Unexpected token in JSON at position 4"
#guard refusal "{a:1}" == "Unexpected token in JSON at position 1"
#guard refusal "1 2" == "Unexpected token in JSON at position 2"
#guard refusal "trueX" == "Unexpected token in JSON at position 4"

/-! ## QuoteJSONString -/

#guard quoteJsonString "" == "\"\""
#guard quoteJsonString "a" == "\"a\""
#guard quoteJsonString "\"\\\n" == "\"\\\"\\\\\\n\""
#guard quoteJsonString "\r\t" == "\"\\r\\t\""
#guard quoteJsonString (String.ofList [Char.ofNat 8, Char.ofNat 12]) == "\"\\b\\f\""
-- Every other code unit below U+0020 is a four-digit escape in lower
-- case, and nothing above it is escaped at all.
#guard quoteJsonString (String.ofList [Char.ofNat 0, Char.ofNat 31]) == "\"\\u0000\\u001f\""
#guard quoteJsonString "é" == "\"é\""
