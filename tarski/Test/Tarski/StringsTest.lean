import Tarski.Eval
import Tarski.Format

/-! String primitives: concatenation, order, `length`, indexing, and
`String(value)`.

Strings here are Lean `String`s, which are sequences of code points: a
lone surrogate cannot live in one, so `length`, indexing, and the
relational order are code-point semantics that happen to agree with
UTF-16 on every string this slice can build. `String.prototype`, the
wrapper object, and the UTF-16 difference are #391's, which is why
`new String("x")` refuses here and every case below is ASCII.

ToNumber of a string is the library's StringToNumber, so a mixed-type
relation like `"a" < 1` is a real comparison that answers `false` because
`"a"` is NaN, and `" 2 " * 3` is `6`. -/

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

/-! ## Concatenation

`+` is concatenation when *either* operand is a string, and the other
side is ToString'd — through the provisional formatter for a number. -/

-- `"a" + "b";`
#guard outcome (expr (.binary .add (.strLit "a") (.strLit "b"))) == "ab"

-- `"n=" + 3;`
#guard outcome (expr (.binary .add (.strLit "n=") (.numLit 3.0))) == "n=3"

-- `1 + "a";`
#guard outcome (expr (.binary .add (.numLit 1.0) (.strLit "a"))) == "1a"

-- `"" + true;`
#guard outcome (expr (.binary .add (.strLit "") (.boolLit true))) == "true"

-- `"x" + null;`
#guard outcome (expr (.binary .add (.strLit "x") .nullLit)) == "xnull"

-- `"x" + undefined;`
#guard outcome (expr (.binary .add (.strLit "x") .undefLit)) == "xundefined"

/-! ## Order

Two strings compare by code point, which is not numeric order: `"10"`
precedes `"9"`. One string and one number go numeric, through
StringToNumber. -/

-- `"a" < "b";`
#guard outcome (expr (.binary .lt (.strLit "a") (.strLit "b"))) == "true"

-- `"b" < "a";`
#guard outcome (expr (.binary .lt (.strLit "b") (.strLit "a"))) == "false"

-- `"a" < "ab";` — a prefix precedes what extends it.
#guard outcome (expr (.binary .lt (.strLit "a") (.strLit "ab"))) == "true"

-- `"" < "a";`
#guard outcome (expr (.binary .lt (.strLit "") (.strLit "a"))) == "true"

-- `"10" < "9";` — string order, not numeric.
#guard outcome (expr (.binary .lt (.strLit "10") (.strLit "9"))) == "true"

-- `"a" <= "a";`
#guard outcome (expr (.binary .le (.strLit "a") (.strLit "a"))) == "true"

-- `"b" > "a";`
#guard outcome (expr (.binary .gt (.strLit "b") (.strLit "a"))) == "true"

-- `"a" >= "b";`
#guard outcome (expr (.binary .ge (.strLit "a") (.strLit "b"))) == "false"

-- `"a" < 1;` — mixed operands go numeric, and `"a"` is NaN, so this is
-- false the way every comparison with a NaN is.
#guard outcome (expr (.binary .lt (.strLit "a") (.numLit 1.0))) == "false"

-- `"10" < 9;` — numeric, not string order: the opposite of `"10" < "9"`.
#guard outcome (expr (.binary .lt (.strLit "10") (.numLit 9.0))) == "false"

-- `"1" < 2;`
#guard outcome (expr (.binary .lt (.strLit "1") (.numLit 2.0))) == "true"

-- `"" < 1;` — the empty string is `+0`.
#guard outcome (expr (.binary .lt (.strLit "") (.numLit 1.0))) == "true"

-- `" 2 " * 3;` — white space at both ends is trimmed.
#guard outcome (expr (.binary .mul (.strLit " 2 ") (.numLit 3.0))) == "6"

-- `"0x10" - 0;` — the non-decimal forms of the literal grammar.
#guard outcome (expr (.binary .sub (.strLit "0x10") (.numLit 0.0))) == "16"

/-! ## `length` and indexing

A string's own properties are its `length` and its index keys. A key
that is not a canonical array index is an ordinary key, and every
ordinary key is `undefined` until `String.prototype` exists (#391). -/

-- `"abc".length;`
#guard outcome (expr (.member (.strLit "abc") "length")) == "3"

-- `"".length;`
#guard outcome (expr (.member (.strLit "") "length")) == "0"

-- `"abc"[1];`
#guard outcome (expr (.index (.strLit "abc") (.numLit 1.0))) == "b"

-- `"abc"["1"];` — the same property under its string spelling.
#guard outcome (expr (.index (.strLit "abc") (.strLit "1"))) == "b"

-- `"abc"[3];`
#guard outcome (expr (.index (.strLit "abc") (.numLit 3.0))) == "undefined"

-- `"abc"["01"];` — not a canonical index, so an ordinary key.
#guard outcome (expr (.index (.strLit "abc") (.strLit "01"))) == "undefined"

-- `"abc".foo;`
#guard outcome (expr (.member (.strLit "abc") "foo")) == "undefined"

-- `"abc".length = 1;` — strict mode: a write to a primitive throws.
#guard outcome (expr (.assign (.member (.strLit "abc") "length") (.numLit 1.0)))
  == "uncaught: TypeError: Cannot set properties of abc (setting 'length')"

/-! ## `String(value)`

ToString and nothing more: the wrapper object is #391's, so `String` has
no `prototype` and `new String("x")` is not a construction. The number arm
is the library's `Number::toString`. -/

/-- `String(<arg>);` -/
private def stringOf (args : List Expr) : Program :=
  expr (.call (.ident "String") args)

#guard outcome (stringOf [.numLit 1.0]) == "1"
#guard outcome (stringOf [.numLit 2.5]) == "2.5"
#guard outcome (stringOf [.unary .neg (.numLit 0.0)]) == "0"
#guard outcome (stringOf [.binary .div (.numLit 0.0) (.numLit 0.0)]) == "NaN"
#guard outcome (stringOf [.boolLit true]) == "true"
#guard outcome (stringOf [.nullLit]) == "null"
#guard outcome (stringOf [.undefLit]) == "undefined"
#guard outcome (stringOf []) == ""
#guard outcome (stringOf [.strLit "x"]) == "x"
#guard outcome (stringOf [.binary .div (.numLit 1.0) (.numLit 3.0)]) == "0.3333333333333333"

-- `typeof String(1);`
#guard outcome (expr (.unary .typeof (.call (.ident "String") [.numLit 1.0]))) == "string"

-- `const o = { toString: function () { return "t"; } }; String(o);` —
-- the string hint tries `toString` first. Method shorthand is #395's, so
-- the member is a function expression.
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit
        [("toString", .funcExpr none [] [.returnStmt (some (.strLit "t"))])]) }],
      .exprStmt (.call (.ident "String") [.ident "o"]) ]
  == "t"

-- `String({});` — `Object.prototype.toString` is what the string hint
-- reaches first.
#guard outcome (stringOf [.objectLit []]) == "[object Object]"

-- `new String("x");` — pinned as pre-#391.
#guard outcome (expr (.new (.ident "String") [.strLit "x"]))
  == "uncaught: TypeError: not a constructor"

-- `typeof String;`
#guard outcome (expr (.unary .typeof (.ident "String"))) == "function"
