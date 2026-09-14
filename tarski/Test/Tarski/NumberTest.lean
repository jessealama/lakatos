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

Two placeholders are pinned here rather than hidden. ToNumber of a string
is NaN (#388), so `Number("12")` and `2 ** "3"` are NaN; and
`Number.prototype.toString` prints the placeholder's decimal string for
*every* radix while still refusing a radix outside 2–36, so
`(255).toString(16)` is `"255"` where an engine answers `"ff"`. #388
replaces one function and both rows move. -/

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
is NaN. ToNumber of a string is still the placeholder (#388). -/

#guard outcome (expr (numberCall [])) == "0"
#guard outcome (expr (numberCall [.undefLit])) == "NaN"
#guard outcome (expr (numberCall [.nullLit])) == "0"
#guard outcome (expr (numberCall [.boolLit true])) == "1"
#guard outcome (expr (numberCall [.boolLit false])) == "0"
#guard outcome (expr (.unary .typeof (numberCall [.numLit 1.0]))) == "number"

-- `Number("12");` — the string arm of ToNumber is #388's placeholder.
#guard outcome (expr (numberCall [.strLit "12"])) == "NaN"

-- `Number({ valueOf: function () { return 7; } });`
#guard outcome
    (expr (numberCall
      [.objectLit [("valueOf", .funcExpr none [] [.returnStmt (some (.numLit 7.0))])]]))
  == "7"

-- `Number({});` — pinned as pre-#389: `Object.prototype` has neither
-- `valueOf` nor `toString` yet, so ToPrimitive has nothing to call.
#guard outcome (expr (numberCall [.objectLit []]))
  == "uncaught: TypeError: Cannot convert object to primitive value"

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

A primitive receiver and a wrapper receiver take the same path. The radix
is validated for real; the output is the placeholder's decimal string for
every radix, radix 10 included — which is the only one it gets right. -/

#guard outcome (expr (.call (.member (.numLit 5.0) "toString") [])) == "5"
#guard outcome (expr (.call (.member (.numLit 1.0) "toString") [.numLit 10.0])) == "1"

-- `(255).toString(16);` — **the placeholder**: JavaScript answers `"ff"`.
-- #388 replaces `formatNumber` and this row moves.
#guard outcome (expr (.call (.member (.numLit 255.0) "toString") [.numLit 16.0])) == "255"

-- `(1).toString(2.5);` — the radix is truncated to 2, which is in range,
-- so the placeholder's decimal string comes back rather than a refusal.
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

/-! ## What `Number` and `Number.prototype` do not have

The `toFixed` family, `toLocaleString`, `parseFloat`, and `parseInt` are
#388's. They are absent rather than faked, so each reads `undefined`. -/

#guard outcome (expr (.member (numberProp "prototype") "toFixed")) == "undefined"
#guard outcome (expr (.member (numberProp "prototype") "toPrecision")) == "undefined"
#guard outcome (expr (.member (numberProp "prototype") "toExponential")) == "undefined"
#guard outcome (expr (.member (numberProp "prototype") "toLocaleString")) == "undefined"
#guard outcome (expr (numberProp "parseFloat")) == "undefined"
#guard outcome (expr (numberProp "parseInt")) == "undefined"

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
string operand (#388) and for a non-integral exponent (#434) is the
same one. -/

-- `2 ** 3 ** 2;` is `2 ** (3 ** 2)`, so 512 rather than 64.
#guard outcome (expr (pow (.numLit 2.0) (pow (.numLit 3.0) (.numLit 2.0)))) == "512"

-- `(-2) ** 2;`
#guard outcome (expr (pow (.unary .neg (.numLit 2.0)) (.numLit 2.0))) == "4"

-- `2 ** "3";` — ToNumber of a string is #388's placeholder.
#guard outcome (expr (pow (.numLit 2.0) (.strLit "3"))) == "NaN"
