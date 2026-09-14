import Tarski.Eval
import Tarski.Format

/-! The `String` surface: `String`'s three statics and
`String.prototype`'s thirty-one methods, reached through the evaluator.

`Test/Js/StringTest.lean` is the other side — what each method *computes*,
as a total function on `JsString`. This file is what the evaluator adds:
the receiver coerced first and the arguments left to right, the generic
receivers, and the six refusals. There is one `#guard` per member, and
the issue's own example is the first of them.

Every method but `toString` and `valueOf` is generic — RequireObjectCoercible
then ToString — so `String.prototype.indexOf.call(123, "2")` is `1`; the
two that are not accept a String primitive or a String object and nothing
else. `Test/Tarski/StringWrapperTest.lean` is the wrapper object itself. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- A program that is one expression. -/
private def expr (e : Expr) : Program := [.exprStmt e]

/-- `recv.name(args...)`. -/
private def m (recv : Expr) (name : String) (args : List Expr) : Expr :=
  .call (.member recv name) args

/-- `String.name(args...)`. -/
private def st (name : String) (args : List Expr) : Expr :=
  m (.ident "String") name args

/-- `String.prototype.name.call(recv, args...)`. -/
private def generic (name : String) (recv : Expr) (args : List Expr) : Expr :=
  m (.member (.member (.ident "String") "prototype") name) "call" (recv :: args)

/-! ## The issue's example

```js
"Hello".toUpperCase() === "HELLO" && "a,b".split(",").length === 2 &&
  "abc".at(-1) === "c" && "x".padStart(3, "ab") === "abx" &&
  "\u{1F600}".length === 2 && "abc".codePointAt(1) === 98 &&
  String.fromCharCode(65) === "A";
```
-/

private def eq (a b : Expr) : Expr := .binary .strictEq a b

#guard outcome (expr
    (.logical .and (eq (m (.strLit "Hello") "toUpperCase" []) (.strLit "HELLO"))
      (.logical .and (eq (.member (m (.strLit "a,b") "split" [.strLit ","]) "length") (.numLit 2.0))
        (.logical .and (eq (m (.strLit "abc") "at" [.numLit (-1.0)]) (.strLit "c"))
          (.logical .and (eq (m (.strLit "x") "padStart" [.numLit 3.0, .strLit "ab"]) (.strLit "abx"))
            (.logical .and (eq (.member (.strLit "😀") "length") (.numLit 2.0))
              (.logical .and (eq (m (.strLit "abc") "codePointAt" [.numLit 1.0]) (.numLit 98.0))
                (eq (st "fromCharCode" [.numLit 65.0]) (.strLit "A")))))))))
  == "true"

/-! ## The three statics -/

#guard outcome (expr (st "fromCharCode" [.numLit 65.0, .numLit 66.0])) == "AB"
#guard outcome (expr (st "fromCharCode" [])) == ""
-- The two halves of a pair, joined.
#guard outcome (expr (eq (st "fromCharCode" [.numLit 55357.0, .numLit 56832.0]) (.strLit "😀")))
  == "true"
-- ToUint16 wraps, so 65601 is `A`.
#guard outcome (expr (st "fromCharCode" [.numLit 65601.0])) == "A"
#guard outcome (expr (eq (st "fromCodePoint" [.numLit 128512.0]) (.strLit "😀"))) == "true"
#guard outcome (expr (st "fromCodePoint" [.numLit 1114112.0]))
  == "uncaught: RangeError: Invalid code point 1114112"
#guard outcome (expr (st "fromCodePoint" [.numLit 1.5]))
  == "uncaught: RangeError: Invalid code point 1.5"
-- `String.raw` reads `raw` off its first argument through `Get`.
#guard outcome (expr
    (st "raw" [.objectLit [.init "raw" (.arrayLit [.strLit "a", .strLit "b"])], .numLit 1.0]))
  == "a1b"

/-! ## Reading a string: `at`, `charAt`, `charCodeAt`, `codePointAt` -/

#guard outcome (expr (m (.strLit "abc") "at" [.numLit (-1.0)])) == "c"
#guard outcome (expr (m (.strLit "abc") "at" [.numLit 3.0])) == "undefined"
#guard outcome (expr (m (.strLit "abc") "charAt" [.numLit 1.0])) == "b"
#guard outcome (expr (m (.strLit "abc") "charAt" [.numLit 9.0])) == ""
#guard outcome (expr (m (.strLit "abc") "charCodeAt" [.numLit 1.0])) == "98"
#guard outcome (expr (m (.strLit "abc") "charCodeAt" [.numLit 9.0])) == "NaN"
-- The low half of a pair is a code unit of its own.
#guard outcome (expr (m (.strLit "😀") "charCodeAt" [.numLit 1.0])) == "56832"
#guard outcome (expr (m (.strLit "abc") "codePointAt" [.numLit 1.0])) == "98"
#guard outcome (expr (m (.strLit "😀") "codePointAt" [.numLit 0.0])) == "128512"
#guard outcome (expr (m (.strLit "abc") "codePointAt" [.numLit 9.0])) == "undefined"

/-! ## Joining, searching, and testing -/

#guard outcome (expr (m (.strLit "a") "concat" [.strLit "b", .numLit 1.0, .nullLit])) == "ab1null"
#guard outcome (expr (m (.strLit "abc") "endsWith" [.strLit "bc"])) == "true"
#guard outcome (expr (m (.strLit "abc") "endsWith" [.strLit "c", .numLit 2.0])) == "false"
#guard outcome (expr (m (.strLit "abc") "includes" [.strLit "b"])) == "true"
#guard outcome (expr (m (.strLit "abc") "includes" [.strLit "b", .numLit 2.0])) == "false"
#guard outcome (expr (m (.strLit "abcabc") "indexOf" [.strLit "bc", .numLit 2.0])) == "4"
#guard outcome (expr (m (.strLit "abc") "indexOf" [.strLit "z"])) == "-1"
#guard outcome (expr (m (.strLit "abcabc") "lastIndexOf" [.strLit "bc", .numLit 3.0])) == "1"
-- A NaN position is `+∞`, so the search starts at the end.
#guard outcome (expr (m (.strLit "abcabc") "lastIndexOf" [.strLit "bc", .strLit "x"])) == "4"
#guard outcome (expr (m (.strLit "abc") "startsWith" [.strLit "b", .numLit 1.0])) == "true"
#guard outcome (expr (m (.strLit "a") "localeCompare" [.strLit "b"])) == "-1"
#guard outcome (expr (m (.strLit "a") "localeCompare" [.strLit "a"])) == "0"
#guard outcome (expr (m (.strLit "b") "localeCompare" [.strLit "a"])) == "1"
#guard outcome (expr (m (.strLit "😀") "isWellFormed" [])) == "true"

/-! ## Slicing and padding -/

#guard outcome (expr (m (.strLit "abcde") "slice" [.numLit 1.0, .numLit (-1.0)])) == "bcd"
#guard outcome (expr (m (.strLit "abcde") "slice" [.numLit 4.0, .numLit 1.0])) == ""
#guard outcome (expr (m (.strLit "abcde") "substring" [.numLit 3.0, .numLit 1.0])) == "bc"
#guard outcome (expr (m (.strLit "abc") "substring" [.numLit (-1.0)])) == "abc"
#guard outcome (expr (m (.strLit "x") "padStart" [.numLit 3.0, .strLit "ab"])) == "abx"
#guard outcome (expr (m (.strLit "x") "padEnd" [.numLit 3.0, .strLit "ab"])) == "xab"
#guard outcome (expr (m (.strLit "x") "padStart" [.numLit 3.0])) == "  x"
#guard outcome (expr (m (.strLit "ab") "repeat" [.numLit 3.0])) == "ababab"
#guard outcome (expr (m (.strLit "ab") "repeat" [.numLit 0.0])) == ""

/-! ## Splitting and replacing -/

#guard outcome
    (expr (m (m (.strLit "a,b,,c") "split" [.strLit ",", .numLit 3.0]) "join" [.strLit "|"]))
  == "a|b|"
#guard outcome (expr (.member (m (.strLit "abc") "split" [.strLit ""]) "length")) == "3"
#guard outcome (expr (.member (m (.strLit "abc") "split" []) "length")) == "1"
#guard outcome (expr (.member (m (.strLit "abc") "split" [.strLit ",", .numLit 0.0]) "length"))
  == "0"
#guard outcome (expr (m (.strLit "xyx") "replace" [.strLit "x", .strLit "z"])) == "zyx"
#guard outcome (expr (m (.strLit "xyx") "replaceAll" [.strLit "x", .strLit "z"])) == "zyz"
-- GetSubstitution: `$&` is the match, and `$$` is a dollar.
#guard outcome (expr (m (.strLit "x") "replace" [.strLit "x", .strLit "$&$&"])) == "xx"
#guard outcome (expr (m (.strLit "ab") "replaceAll" [.strLit "", .strLit "-"])) == "-a-b-"
-- A callable replacer is called with `(matched, position, string)`.
#guard outcome
    (expr (m (.strLit "xyx") "replace"
      [.strLit "x",
       .funcExpr none ["a", "b", "c"]
         [.returnStmt (some (.binary .add (.binary .add (.ident "a") (.ident "b")) (.ident "c")))]]))
  == "x0xyxyx"

/-! ## Case, trimming, normalization, and well-formedness -/

#guard outcome (expr (m (.strLit "aB") "toUpperCase" [])) == "AB"
#guard outcome (expr (m (.strLit "aB") "toLowerCase" [])) == "ab"
#guard outcome (expr (m (.strLit "aB") "toLocaleUpperCase" [])) == "AB"
#guard outcome (expr (m (.strLit "aB") "toLocaleLowerCase" [])) == "ab"
-- Case mapping is ASCII-only: Lean has no Unicode character database,
-- and #518 owns the rest.
#guard outcome (expr (m (.strLit "aé") "toUpperCase" [])) == "Aé"
#guard outcome (expr (m (.strLit " a ") "trim" [])) == "a"
#guard outcome (expr (m (.strLit " a ") "trimStart" [])) == "a "
#guard outcome (expr (m (.strLit " a ") "trimEnd" [])) == " a"
#guard outcome (expr (m (.strLit "a") "normalize" [])) == "a"
#guard outcome (expr (m (.strLit "a") "normalize" [.strLit "NFKD"])) == "a"
#guard outcome (expr (m (.strLit "a") "normalize" [.strLit "nfc"]))
  == "uncaught: RangeError: The normalization form should be one of NFC, NFD, NFKC, NFKD."
#guard outcome (expr (m (.strLit "abc") "toWellFormed" [])) == "abc"
#guard outcome (expr (m (.strLit "x") "toString" [])) == "x"
#guard outcome (expr (m (.strLit "x") "valueOf" [])) == "x"

/-! ## Generic receivers

Every method but `toString` and `valueOf` is RequireObjectCoercible then
ToString, so a Number receiver works. -/

#guard outcome (expr (generic "indexOf" (.numLit 123.0) [.strLit "2"])) == "1"
#guard outcome (expr (generic "toUpperCase" (.boolLit true) [])) == "TRUE"

/-! ## The refusals -/

#guard outcome (expr (generic "trim" .nullLit []))
  == "uncaught: TypeError: String.prototype.trim called on null or undefined"
#guard outcome (expr (generic "at" .undefLit [.numLit 0.0]))
  == "uncaught: TypeError: String.prototype.at called on null or undefined"
#guard outcome (expr (generic "toString" (.numLit 1.0) []))
  == "uncaught: TypeError: String.prototype.toString requires that 'this' be a String"
#guard outcome (expr (generic "valueOf" (.objectLit []) []))
  == "uncaught: TypeError: String.prototype.valueOf requires that 'this' be a String"
#guard outcome (expr (m (.strLit "x") "repeat" [.numLit (-1.0)]))
  == "uncaught: RangeError: Invalid count value: -1"
#guard outcome (expr (m (.strLit "x") "repeat" [.binary .div (.numLit 1.0) (.numLit 0.0)]))
  == "uncaught: RangeError: Invalid count value: Infinity"

/-! ## Coercion order

The receiver first, then the arguments left to right: `padStart` reports
the `valueOf` that threw on its `maxLength`, not the `toString` on its
filler. -/

private def thrower (method : String) (kind : String) (msg : String) : Expr :=
  .objectLit
    [.init method (.funcExpr none []
      [.throwStmt (.new (.ident kind) [.strLit msg])])]

#guard outcome (expr (m (.strLit "a") "padStart"
    [thrower "valueOf" "RangeError" "first", thrower "toString" "TypeError" "second"]))
  == "uncaught: RangeError: first"
