import Tarski.Eval
import Tarski.Format

/-! The `Number` intrinsic, the Number wrapper object, and `**`.

`Number` is two things at once: a conversion when called and a wrapper
constructor when `new`ed, off one ToNumber. The four predicates are the
library's, and they do not coerce. The eight constants are the library's
own definitions under their source spellings, so the identities the issue
names — `Number.EPSILON === 2 ** -52`,
`Number.isSafeInteger(2 ** 53 - 1)` — are about the same doubles a
`Theorem` is about.

A Number primitive reads its properties through `Number.prototype`
without a wrapper ever being allocated, and the receiver a method then
sees is the primitive itself; `thisNumberValue` accepts both, which is
what makes `(5).toString()` and `new Number(5).toString()` one path.

ToNumber of a string, ToString of a number, and the five formatters are
the library's definitions (`Js/Number/ToString.lean`,
`Js/Number/StringToNumber.lean`), so what is checked here is the
dispatch — the receiver, the argument order, the range checks, and their
messages — rather than the digits, which `Test/Js/NumberToStringTest.lean`
pins against an engine. -/

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

/-- `-0`. -/
private def negZero : Expr := .unary .neg (.numLit 0.0)

/-- `Number(<args>);` -/
private def numberCall (args : List Expr) : Expr := .call (.ident "Number") args

/-- `Number.<name>(<args>);` -/
private def numberMember (name : String) (args : List Expr) : Expr :=
  .call (.member (.ident "Number") name) args

/-- `Number.<name>` — a constant, or an absent member. -/
private def numberProp (name : String) : Expr := .member (.ident "Number") name

/-- `Math.<name>(<args>);` -/
private def math (name : String) (args : List Expr) : Expr :=
  .call (.member (.ident "Math") name) args

/-- `Object.is(<a>, <b>);` -/
private def objectIs (a b : Expr) : Expr := .call (.member (.ident "Object") "is") [a, b]

/-- `<base> ** <exponent>`. -/
private def pow (base exponent : Expr) : Expr := .binary .exponent base exponent

/-- `2 ** 53`. -/
private def twoTo53 : Expr := pow (.numLit 2.0) (.numLit 53.0)

/-! ## The issue's own example

```js
Math.fround(0.1) === 0.10000000149011612 && Number.isSafeInteger(2 ** 53 - 1) === true &&
  Object.is(Math.round(-0.4), -0) && Math.max(NaN, 1) !== Math.max(NaN, 1) &&
  Number.EPSILON === 2 ** -52;
```

`tarski/Test/Tarski/fixtures/number-math.json` is the same program
arriving through the parser bridge, and the workflow runs the binary on
it. -/

#guard outcome
    (expr (.logical .and
      (.logical .and
        (.logical .and
          (.logical .and
            (.binary .strictEq (math "fround" [.numLit 0.1]) (.numLit 0.10000000149011612))
            (.binary .strictEq
              (numberMember "isSafeInteger"
                [.binary .sub twoTo53 (.numLit 1.0)])
              (.boolLit true)))
          (objectIs (math "round" [.unary .neg (.numLit 0.4)]) negZero))
        (.binary .strictNe (math "max" [.ident "NaN", .numLit 1.0])
          (math "max" [.ident "NaN", .numLit 1.0])))
      (.binary .strictEq (numberProp "EPSILON") (pow (.numLit 2.0) (.unary .neg (.numLit 52.0))))))
  == "true"

/-! ## `Number` as a conversion

A *missing* argument is `+0`; an argument that is present and `undefined`
is NaN. -/

#guard outcome (expr (numberCall [])) == "0"
#guard outcome (expr (numberCall [.undefLit])) == "NaN"
#guard outcome (expr (numberCall [.nullLit])) == "0"
#guard outcome (expr (numberCall [.boolLit true])) == "1"
#guard outcome (expr (numberCall [.boolLit false])) == "0"
#guard outcome (expr (.unary .typeof (numberCall [.numLit 1.0]))) == "number"

-- `Number("12");` — the string arm of ToNumber is StringToNumber.
#guard outcome (expr (numberCall [.strLit "12"])) == "12"
#guard outcome (expr (numberCall [.strLit ""])) == "0"
#guard outcome (expr (numberCall [.strLit " "])) == "0"
#guard outcome (expr (numberCall [.strLit "0x1F"])) == "31"
-- A numeric separator is not in the literal grammar StringToNumber reads.
#guard outcome (expr (numberCall [.strLit "1_0"])) == "NaN"

-- `Number({ valueOf: function () { return 7; } });`
#guard outcome
    (expr (numberCall
      [.objectLit [("valueOf", .funcExpr none [] [.returnStmt (some (.numLit 7.0))])]]))
  == "7"

-- `Number({});` — ToPrimitive gives `"[object Object]"`, whose
-- StringToNumber is NaN.
#guard outcome (expr (numberCall [.objectLit []])) == "NaN"

/-! ## `new Number(v)`, the wrapper object

One conversion, two answers: `Number(v)` is the Number and
`new Number(v)` is an object around it. `[[NumberData]]` is a field rather
than a property, so it is not enumerable and no write can forge one. -/

#guard outcome (expr (.unary .typeof (.new (.ident "Number") [.numLit 1.0]))) == "object"
#guard outcome (expr (.binary .add (.new (.ident "Number") [.numLit 3.0]) (.numLit 1.0))) == "4"
#guard outcome
    (expr (.binary .strictEq (.new (.ident "Number") [.numLit 3.0]) (.numLit 3.0))) == "false"
#guard outcome
    (expr (.binary .strictEq
      (.call (.member (.new (.ident "Number") [.numLit 3.0]) "valueOf") []) (.numLit 3.0)))
  == "true"

-- `new Number().valueOf();` — the missing argument is `+0` here too.
#guard outcome (expr (.call (.member (.new (.ident "Number") []) "valueOf") [])) == "0"

-- `Object.is(new Number(-0).valueOf(), -0);` — the sign survives the box.
#guard outcome
    (expr (objectIs (.call (.member (.new (.ident "Number") [negZero]) "valueOf") []) negZero))
  == "true"

-- `String(new Number(3));` — the string hint reaches `toString`.
#guard outcome (expr (.call (.ident "String") [.new (.ident "Number") [.numLit 3.0]])) == "3"

#guard outcome
    (expr (.binary .instanceof (.new (.ident "Number") [.numLit 1.0]) (.ident "Number")))
  == "true"
#guard outcome
    (expr (.binary .instanceof (.new (.ident "Number") [.numLit 1.0]) (.ident "Object")))
  == "true"
#guard outcome
    (expr (.binary .instanceof (numberProp "prototype") (.ident "Number"))) == "false"

-- `Object.keys(new Number(1)).length;` — `[[NumberData]]` is not a key.
#guard outcome
    (expr (.member (.call (.member (.ident "Object") "keys")
      [.new (.ident "Number") [.numLit 1.0]]) "length"))
  == "0"

#guard outcome (expr (.unary .typeof (.ident "Number"))) == "function"

/-! ## `Number.prototype.toString` and `valueOf`

A primitive receiver and a wrapper receiver take the same path. Radix 10
is `Number::toString`; every other radix in 2–36 is the library's
generalization of it. -/

#guard outcome (expr (.call (.member (.numLit 5.0) "toString") [])) == "5"
#guard outcome (expr (.call (.member (.numLit 1.0) "toString") [.numLit 10.0])) == "1"

-- `(255).toString(16);`
#guard outcome (expr (.call (.member (.numLit 255.0) "toString") [.numLit 16.0])) == "ff"
#guard outcome (expr (.call (.member (.numLit 255.0) "toString") [.numLit 2.0])) == "11111111"
#guard outcome (expr (.call (.member (.unary .neg (.numLit 255.0)) "toString") [.numLit 36.0]))
  == "-73"
#guard outcome (expr (.call (.member (.numLit 0.5) "toString") [.numLit 2.0])) == "0.1"
#guard outcome (expr (.call (.member (.numLit 35.0) "toString") [.numLit 36.0])) == "z"
#guard outcome (expr (.call (.member (.ident "NaN") "toString") [.numLit 2.0])) == "NaN"

-- `Number.prototype.toString(2);` — the prototype's `[[NumberData]]` is `+0`.
#guard outcome (expr (.call (.member (numberProp "prototype") "toString") [.numLit 2.0])) == "0"

-- `new Number(-1).toString(2);`
#guard outcome
    (expr (.call (.member (.new (.ident "Number") [.unary .neg (.numLit 1.0)]) "toString")
      [.numLit 2.0]))
  == "-1"

-- `(1).toString(2.5);` — the radix is truncated to 2, which is in range.
#guard outcome (expr (.call (.member (.numLit 1.0) "toString") [.numLit 2.5])) == "1"

-- A radix outside 2–36 is a real `RangeError`, from every direction.
#guard outcome (expr (.call (.member (.numLit 1.0) "toString") [.numLit 1.0]))
  == "uncaught: RangeError: toString() radix must be between 2 and 36"
#guard outcome (expr (.call (.member (.numLit 1.0) "toString") [.numLit 37.0]))
  == "uncaught: RangeError: toString() radix must be between 2 and 36"
#guard outcome (expr (.call (.member (.numLit 1.0) "toString") [.ident "Infinity"]))
  == "uncaught: RangeError: toString() radix must be between 2 and 36"
#guard outcome (expr (.call (.member (.numLit 1.0) "toString") [.ident "NaN"]))
  == "uncaught: RangeError: toString() radix must be between 2 and 36"

-- `Number.prototype.valueOf();` — the prototype is itself a Number object
-- of value `+0`, as the spec has it.
#guard outcome (expr (.call (.member (numberProp "prototype") "valueOf") [])) == "0"

-- `const f = Number.prototype.valueOf; f();` — detached, so `this` is
-- `undefined` and the method refuses by name.
#guard outcome
    [ .varDecl .«const» [{ name := "f", init := some (.member (numberProp "prototype") "valueOf") }],
      .exprStmt (.call (.ident "f") []) ]
  == "uncaught: TypeError: Number.prototype.valueOf requires that 'this' be a Number"
#guard outcome
    [ .varDecl .«const» [{ name := "g", init := some (.member (numberProp "prototype") "toString") }],
      .exprStmt (.call (.ident "g") []) ]
  == "uncaught: TypeError: Number.prototype.toString requires that 'this' be a Number"


/-! ## The four predicates, which do not coerce -/

#guard outcome (expr (numberMember "isFinite" [.numLit 1.0])) == "true"
#guard outcome (expr (numberMember "isFinite" [.ident "Infinity"])) == "false"
#guard outcome (expr (numberMember "isFinite" [.strLit "1"])) == "false"
#guard outcome (expr (numberMember "isFinite" [])) == "false"

#guard outcome (expr (numberMember "isNaN" [.ident "NaN"])) == "true"
#guard outcome (expr (numberMember "isNaN" [.strLit "NaN"])) == "false"
-- A wrapper is an object, not a Number, so this is `false` too.
#guard outcome (expr (numberMember "isNaN" [.new (.ident "Number") [.ident "NaN"]])) == "false"

#guard outcome (expr (numberMember "isInteger" [.numLit 2.5])) == "false"
#guard outcome (expr (numberMember "isInteger" [negZero])) == "true"
#guard outcome (expr (numberMember "isInteger" [.ident "Infinity"])) == "false"

#guard outcome (expr (numberMember "isSafeInteger" [twoTo53])) == "false"
#guard outcome (expr (numberMember "isSafeInteger" [.binary .sub twoTo53 (.numLit 1.0)])) == "true"
#guard outcome
    (expr (numberMember "isSafeInteger" [.unary .neg (.binary .sub twoTo53 (.numLit 1.0))]))
  == "true"

/-! ## The eight constants, each the library's own definition -/

#guard outcome
    (expr (.binary .strictEq (numberProp "EPSILON") (pow (.numLit 2.0) (.unary .neg (.numLit 52.0)))))
  == "true"
#guard outcome
    (expr (.binary .strictEq (numberProp "MAX_SAFE_INTEGER") (.numLit 9007199254740991.0)))
  == "true"
#guard outcome
    (expr (.binary .strictEq (numberProp "MIN_SAFE_INTEGER")
      (.unary .neg (.numLit 9007199254740991.0))))
  == "true"
#guard outcome
    (expr (.binary .strictEq (numberProp "MAX_VALUE") (.numLit 1.7976931348623157e308)))
  == "true"
#guard outcome (expr (.binary .strictEq (numberProp "MIN_VALUE") (.numLit 5e-324))) == "true"
#guard outcome (expr (.binary .strictEq (numberProp "POSITIVE_INFINITY") (.ident "Infinity")))
  == "true"
#guard outcome
    (expr (.binary .strictEq (numberProp "NEGATIVE_INFINITY") (.unary .neg (.ident "Infinity"))))
  == "true"
#guard outcome (expr (numberMember "isNaN" [numberProp "NaN"])) == "true"

/-! ## The two global value bindings

`NaN` and `Infinity` are the global object's non-writable value
properties, so their cells are immutable: assignment is the same
strict-mode refusal an assignment to a `const` is. A local declaration may
still shadow either, as it may shadow `Object`. -/

#guard outcome (expr (.binary .strictNe (.ident "NaN") (.ident "NaN"))) == "true"
#guard outcome (expr (.unary .typeof (.ident "NaN"))) == "number"
#guard outcome (expr (.binary .gt (.ident "Infinity") (numberProp "MAX_VALUE"))) == "true"
#guard outcome
    (expr (.binary .lt (.unary .neg (.ident "Infinity"))
      (.unary .neg (numberProp "MAX_VALUE"))))
  == "true"
#guard outcome (expr (.binary .div (.numLit 1.0) (.ident "Infinity"))) == "0"

#guard outcome (expr (.assign (.ident "NaN") (.numLit 1.0)))
  == "uncaught: TypeError: Assignment to constant variable."
#guard outcome
    [ .varDecl .«let» [{ name := "NaN", init := some (.numLit 1.0) }],
      .exprStmt (.ident "NaN") ]
  == "1"

/-! ## A Number primitive as a property base

The read goes through `Number.prototype` and no wrapper is allocated. -/

#guard outcome (expr (.member (.numLit 1.0) "x")) == "undefined"
#guard outcome
    (expr (.binary .strictEq (.member (.numLit 1.0) "constructor") (.ident "Number"))) == "true"
#guard outcome
    (expr (.call (.member (.numLit 1.0) "hasOwnProperty") [.strLit "x"])) == "false"

/-! `let flag = false; const k = { toString: … flag = true … };
(1).hasOwnProperty(k); flag;` — the answer is `false` either way, but the
key is converted *first*, as the spec orders it, so the user `toString`
runs. -/
#guard outcome
    [ .varDecl .«let» [{ name := "flag", init := some (.boolLit false) }],
      .varDecl .«const»
        [ { name := "k",
            init := some (.objectLit
              [ ("toString",
                 .funcExpr none []
                   [ .exprStmt (.assign (.ident "flag") (.boolLit true)),
                     .returnStmt (some (.strLit "x")) ]) ]) } ],
      .exprStmt (.call (.member (.numLit 1.0) "hasOwnProperty") [.ident "k"]),
      .exprStmt (.ident "flag") ]
  == "true"

/-! ## `Object(1)` and `Object("s")` -/

#guard outcome (expr (.unary .typeof (.call (.ident "Object") [.numLit 1.0]))) == "object"
#guard outcome
    (expr (.binary .strictEq
      (.call (.member (.call (.ident "Object") [.numLit 1.0]) "valueOf") []) (.numLit 1.0)))
  == "true"
#guard outcome
    (expr (.binary .instanceof (.call (.ident "Object") [.numLit 1.0]) (.ident "Number")))
  == "true"

-- The String wrapper is #391's, so this still refuses.
#guard outcome (expr (.call (.ident "Object") [.strLit "s"]))
  == "uncaught: TypeError: Cannot convert a primitive to an object"

/-! ## `**`

Right-associativity is the parser's, and is already resolved by the time
the tree arrives; the AST case below is the right-nested one it produces.
`**` and `Math.pow` are one library definition, so the placeholder for a
non-integral exponent (#434) is the same one. -/

-- `2 ** 3 ** 2;` is `2 ** (3 ** 2)`, so 512 rather than 64.
#guard outcome (expr (pow (.numLit 2.0) (pow (.numLit 3.0) (.numLit 2.0)))) == "512"

-- `(-2) ** 2;`
#guard outcome (expr (pow (.unary .neg (.numLit 2.0)) (.numLit 2.0))) == "4"

-- `2 ** "3";` — ToNumber of a string is StringToNumber.
#guard outcome (expr (pow (.numLit 2.0) (.strLit "3"))) == "8"

/-! ## The issue's example

GitHub #388's own acceptance case, as one term:

```js
String(0.1 + 0.2) === "0.30000000000000004" && String(1e21) === "1e+21" &&
  String(123456789012345680000) === "123456789012345680000" &&
  (255).toString(16) === "ff" && Number("0x1F") === 31 &&
  Number("  12e-1 ") === 1.2 && Number.isNaN(Number("1_0")) && Number("") === 0;
```

`Test/Tarski/fixtures/number-conversions.json` is the same script through
the bridge, and the binary prints `true` for it. -/

private def and2 (a b : Expr) : Expr := .logical .and a b

#guard outcome (expr (and2
    (and2
      (and2
        (and2 (.binary .strictEq (.call (.ident "String")
                [.binary .add (.numLit 0.1) (.numLit 0.2)]) (.strLit "0.30000000000000004"))
              (.binary .strictEq (.call (.ident "String") [.numLit 1e21]) (.strLit "1e+21")))
        (and2 (.binary .strictEq (.call (.ident "String") [.numLit 123456789012345680000])
                (.strLit "123456789012345680000"))
              (.binary .strictEq (.call (.member (.numLit 255.0) "toString") [.numLit 16.0])
                (.strLit "ff"))))
      (and2 (.binary .strictEq (numberCall [.strLit "0x1F"]) (.numLit 31.0))
            (.binary .strictEq (numberCall [.strLit "  12e-1 "]) (.numLit 1.2))))
    (and2 (numberMember "isNaN" [numberCall [.strLit "1_0"]])
          (.binary .strictEq (numberCall [.strLit ""]) (.numLit 0.0)))))
  == "true"

/-! ## `String(x)` is `Number::toString`

The digits are the library's and are pinned there; these rows are the
seam — that the evaluator's ToString of a Number is that definition and
not another one. -/

/-- `String(<e>);` -/
private def stringOf (e : Expr) : Expr := .call (.ident "String") [e]

#guard outcome (expr (stringOf (.binary .add (.numLit 0.1) (.numLit 0.2))))
  == "0.30000000000000004"
#guard outcome (expr (stringOf (.numLit 1e21))) == "1e+21"
#guard outcome (expr (stringOf (.numLit 123456789012345680000))) == "123456789012345680000"
#guard outcome (expr (stringOf (.binary .div (.numLit 1.0) (.numLit 3.0))))
  == "0.3333333333333333"
#guard outcome (expr (stringOf (.unary .neg (.numLit 1e-7)))) == "-1e-7"
#guard outcome (expr (stringOf (pow (.numLit 2.0) (.numLit 64.0)))) == "18446744073709552000"

-- A property key is ToString of the Number, so an exponent form is the key.
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
      .exprStmt (.assign (.index (.ident "o") (.numLit 1e21)) (.numLit 1.0)),
      .exprStmt (.call (.member (.call (.member (.ident "Object") "keys") [.ident "o"]) "join") []) ]
  == "1e+21"
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
      .exprStmt (.assign (.index (.ident "o") (.binary .add (.numLit 0.1) (.numLit 0.2)))
        (.numLit 7.0)),
      .exprStmt (.index (.ident "o") (.strLit "0.30000000000000004")) ]
  == "7"

/-! ## `toFixed`, `toExponential`, `toPrecision`, `toLocaleString`

The **specification's step order** is what these rows check. A poisoned
argument is coerced, and so throws, before any range check. A non-finite
`this` short-circuits `toExponential` and `toPrecision` before their range
check but not `toFixed`, so `Infinity.toExponential(200)` is `Infinity`
while `NaN.toFixed(Infinity)` throws. -/

/-- `(<recv>).<name>(<args>);` -/
private def methodOn (recv : Expr) (name : String) (args : List Expr) : Expr :=
  .call (.member recv name) args

/-- `{ valueOf: function () { throw <e>; } }` -/
private def poison (e : Expr) : Expr :=
  .objectLit [("valueOf", .funcExpr none [] [.throwStmt e])]

#guard outcome (expr (methodOn (.numLit 3.0) "toFixed" [.numLit 0.0])) == "3"
#guard outcome (expr (methodOn (.numLit 1000000000000000128) "toFixed" [.numLit 0.0]))
  == "1000000000000000128"
#guard outcome (expr (methodOn (.numLit 1.005) "toFixed" [.numLit 2.0])) == "1.00"
#guard outcome (expr (methodOn (.numLit 1e21) "toFixed" [.numLit 2.0])) == "1e+21"
#guard outcome (expr (methodOn (.ident "NaN") "toFixed" [.numLit 1.0])) == "NaN"
#guard outcome (expr (methodOn (numberProp "prototype") "toFixed" [])) == "0"
#guard outcome (expr (methodOn (numberProp "prototype") "toFixed" [.strLit "1"])) == "0.0"
#guard outcome (expr (methodOn (.numLit 3.0) "toFixed" [.unary .neg (.numLit 1.0)]))
  == "uncaught: RangeError: toFixed() digits argument must be between 0 and 100"
#guard outcome (expr (methodOn (.numLit 3.0) "toFixed" [.numLit 101.0]))
  == "uncaught: RangeError: toFixed() digits argument must be between 0 and 100"
#guard outcome (expr (methodOn (.ident "NaN") "toFixed" [.ident "Infinity"]))
  == "uncaught: RangeError: toFixed() digits argument must be between 0 and 100"

-- The argument is coerced before the range is checked, so its `valueOf`
-- throws first.
#guard outcome
    (expr (methodOn (.numLit 1.0) "toFixed" [poison (.new (.ident "RangeError") [.strLit "v"])]))
  == "uncaught: RangeError: v"

#guard outcome (expr (methodOn (.numLit 123.456) "toExponential" [.numLit 3.0])) == "1.235e+2"
#guard outcome (expr (methodOn (.numLit 25.0) "toExponential" [.numLit 0.0])) == "3e+1"
#guard outcome (expr (methodOn (.numLit 0.0) "toExponential" [])) == "0e+0"
#guard outcome (expr (methodOn (.numLit 123456.0) "toExponential" [])) == "1.23456e+5"
#guard outcome (expr (methodOn (.numLit 123456.0) "toExponential" [.undefLit])) == "1.23456e+5"
-- A non-finite `this` answers before the range check.
#guard outcome (expr (methodOn (.ident "Infinity") "toExponential" [.numLit 200.0])) == "Infinity"
#guard outcome (expr (methodOn (.numLit 1.0) "toExponential" [.numLit 101.0]))
  == "uncaught: RangeError: toExponential() argument must be between 0 and 100"
#guard outcome (expr (methodOn (.numLit 1.0) "toExponential" [.ident "Infinity"]))
  == "uncaught: RangeError: toExponential() argument must be between 0 and 100"

#guard outcome (expr (methodOn (.numLit 7.0) "toPrecision" [.numLit 3.0])) == "7.00"
#guard outcome (expr (methodOn (.numLit 10.0) "toPrecision" [.numLit 1.0])) == "1e+1"
#guard outcome (expr (methodOn (.numLit 123.456) "toPrecision" [.numLit 4.0])) == "123.5"
#guard outcome (expr (methodOn (.numLit 0.0) "toPrecision" [.numLit 3.0])) == "0.00"
#guard outcome (expr (methodOn (.numLit 1.0) "toPrecision" [])) == "1"
#guard outcome (expr (methodOn (.numLit 1.0) "toPrecision" [.undefLit])) == "1"
#guard outcome (expr (methodOn (.ident "Infinity") "toPrecision" [.numLit 200.0])) == "Infinity"
#guard outcome (expr (methodOn (.numLit 1.0) "toPrecision" [.numLit 0.0]))
  == "uncaught: RangeError: toPrecision() argument must be between 1 and 100"
#guard outcome (expr (methodOn (.numLit 1.0) "toPrecision" [.numLit 101.0]))
  == "uncaught: RangeError: toPrecision() argument must be between 1 and 100"

-- There is no locale here, so `toLocaleString` is `toString()`.
#guard outcome (expr (methodOn (.numLit 1234.5) "toLocaleString" [])) == "1234.5"
#guard outcome (expr (methodOn (numberProp "prototype") "toLocaleString" [])) == "0"

-- A poisoned radix throws before anything else: the argument is coerced
-- first, and `NaN` never reaches the formatter.
#guard outcome
    (expr (methodOn (.ident "NaN") "toString" [poison (.new (.ident "Error") [.strLit "p"])]))
  == "uncaught: Error: p"

-- Detached, so `this` is `undefined` and each method refuses by name.
#guard ["toFixed", "toExponential", "toPrecision", "toLocaleString"].all fun name =>
  outcome
      [ .varDecl .«const» [{ name := "f", init := some (.member (numberProp "prototype") name) }],
        .exprStmt (.call (.ident "f") []) ]
    == s!"uncaught: TypeError: Number.prototype.{name} requires that 'this' be a Number"

/-! ## `parseFloat` and `parseInt`

One function object each, bound globally and read off `Number`, as the
specification has them. `parseInt` converts its **string** before its
radix, which is what the log below observes. -/

#guard outcome (expr (.binary .strictEq (numberProp "parseFloat") (.ident "parseFloat"))) == "true"
#guard outcome (expr (.binary .strictEq (numberProp "parseInt") (.ident "parseInt"))) == "true"
#guard outcome (expr (.unary .typeof (.ident "parseInt"))) == "function"
-- Every built-in carries the `length` 17.1 gives it;
-- `Test/Tarski/FunctionBuiltinsTest.lean` pins the attributes.
#guard outcome (expr (.member (.ident "parseInt") "length")) == "2"

#guard outcome (expr (.call (.ident "parseInt") [.strLit "0x1F"])) == "31"
-- ToInt32 of 2^32 is 0, which means radix 10.
#guard outcome (expr (.call (.ident "parseInt") [.strLit "11", pow (.numLit 2.0) (.numLit 32.0)]))
  == "11"
#guard outcome (expr (.call (.ident "parseInt")
    [.strLit "11", .binary .add (pow (.numLit 2.0) (.numLit 32.0)) (.numLit 2.0)]))
  == "3"
#guard outcome (expr (.call (.ident "parseInt") [.nullLit, .numLit 36.0])) == "1112745"
#guard outcome (expr (.call (.ident "parseInt") [.strLit "  42abc"])) == "42"
#guard outcome (expr (.call (.ident "parseInt") [.strLit ""])) == "NaN"
#guard outcome (expr (objectIs (.call (.ident "parseInt") [.strLit "-0"]) negZero)) == "true"
#guard outcome (expr (.call (.ident "parseFloat") [.strLit "  1.5x"])) == "1.5"
#guard outcome (expr (.call (.ident "parseFloat") [.strLit "Infinityx"])) == "Infinity"
#guard outcome (expr (.call (.ident "parseFloat") [.strLit "0x10"])) == "0"
#guard outcome (expr (numberMember "parseInt" [.strLit "12", .numLit 10.0])) == "12"

-- `parseInt`'s string is converted first, so the log reads `sr`.
#guard outcome
    [ .varDecl .«let» [{ name := "log", init := some (.strLit "") }],
      .exprStmt (.call (.ident "parseInt")
        [ .objectLit [("toString", .funcExpr none []
            [ .exprStmt (.assign (.ident "log") (.binary .add (.ident "log") (.strLit "s"))),
              .returnStmt (some (.strLit "1")) ])],
          .objectLit [("valueOf", .funcExpr none []
            [ .exprStmt (.assign (.ident "log") (.binary .add (.ident "log") (.strLit "r"))),
              .returnStmt (some (.numLit 10.0)) ])] ]),
      .exprStmt (.ident "log") ]
  == "sr"
