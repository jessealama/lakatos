import Tarski.Eval
import Tarski.Format

/-! Symbols: the third primitive, the registry, symbol-keyed properties,
and the three well-known symbols whose protocols this slice implements.

A symbol is a `Value` constructor rather than a `Js.JsVal` tag because a
`JsVal` has no identity and two `Symbol("k")` calls are two symbols. What
that buys, and what this file pins, is a key that `Object.keys`,
`for`-`in`, `Object.getOwnPropertyNames`, and `JSON.stringify` all pass
over while `Object.getOwnPropertySymbols`, `in`, `delete`,
`hasOwnProperty`, and `Object.assign` all see.

`@@toPrimitive`, `@@toStringTag`, and `@@hasInstance` have their
semantics here because each is a single step in a definition this slice
already owns. The other ten well-known symbols are values and nothing
more: `@@iterator` waits for #394, `@@species` and
`@@isConcatSpreadable` for #390. -/

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

/-- `const s = Symbol(<args>);` in front of one expression. -/
private def withSymbol (args : List Expr) (e : Expr) : Program :=
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") args) }],
    .exprStmt e ]

/-- `s`, the symbol the two helpers above bind. -/
private def s : Expr := .ident "s"

/-- `const s = Symbol("k"); const o = {}; o[s] = 1;` and then one
expression. -/
private def keyed (e : Expr) : Program :=
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .varDecl .«const» [{ target := "o", init := some (.objectLit [.init "a" (.numLit 0.0)]) }],
    .exprStmt (.assign (.index (.ident "o") s) (.numLit 1.0)),
    .exprStmt e ]

/-! ## A symbol is a primitive with an identity -/

#guard outcome (expr (.unary .typeof (.call (.ident "Symbol") []))) == "symbol"
#guard outcome (withSymbol [] (.binary .strictEq s s)) == "true"

-- Two calls are two symbols, however they are described.
#guard outcome (expr (.binary .strictEq
  (.call (.ident "Symbol") [.strLit "k"]) (.call (.ident "Symbol") [.strLit "k"]))) == "false"
#guard outcome (withSymbol [] (.call (.member (.ident "Object") "is") [s, s])) == "true"

-- A symbol is truthy, and `!s` is therefore `false`.
#guard outcome (withSymbol [] (.unary .not s)) == "false"

/-! ## `description` -/

#guard outcome (withSymbol [.strLit "k"] (.member s "description")) == "k"
#guard outcome (withSymbol [] (.member s "description")) == "undefined"
#guard outcome (withSymbol [.undefLit] (.member s "description")) == "undefined"
#guard outcome (withSymbol [.strLit ""] (.member s "description")) == ""

/-! ## The registry -/

#guard outcome (expr (.binary .strictEq
  (.call (.member (.ident "Symbol") "for") [.strLit "q"])
  (.call (.member (.ident "Symbol") "for") [.strLit "q"]))) == "true"
#guard outcome (expr (.call (.member (.ident "Symbol") "keyFor")
  [.call (.member (.ident "Symbol") "for") [.strLit "q"]])) == "q"
#guard outcome (expr (.call (.member (.ident "Symbol") "keyFor")
  [.call (.ident "Symbol") [.strLit "q"]])) == "undefined"
#guard outcome (expr (.call (.member (.ident "Symbol") "keyFor") [.numLit 1.0]))
  == "uncaught: TypeError: 1 is not a symbol"
-- A registered symbol's description is its key.
#guard outcome (expr (.member (.call (.member (.ident "Symbol") "for") [.strLit "q"])
  "description")) == "q"

/-! ## Text: `String(sym)` is the one route that is not a refusal -/

#guard outcome (withSymbol [.strLit "k"] (.call (.ident "String") [s])) == "Symbol(k)"
#guard outcome (withSymbol [.strLit "k"] (.call (.member s "toString") [])) == "Symbol(k)"
#guard outcome (withSymbol [] (.call (.ident "String") [s])) == "Symbol()"
#guard outcome (withSymbol [.strLit "k"] (.binary .add s (.strLit "")))
  == "uncaught: TypeError: Cannot convert a Symbol value to a string"
#guard outcome (withSymbol [.strLit "k"] (.binary .mul s (.numLit 1.0)))
  == "uncaught: TypeError: Cannot convert a Symbol value to a number"
#guard outcome (withSymbol [.strLit "k"] (.binary .add s (.numLit 1.0)))
  == "uncaught: TypeError: Cannot convert a Symbol value to a number"
#guard outcome (withSymbol [.strLit "k"] (.unary .neg s))
  == "uncaught: TypeError: Cannot convert a Symbol value to a number"

/-! ## The wrapper object -/

#guard outcome (withSymbol [.strLit "k"]
  (.unary .typeof (.call (.ident "Object") [s]))) == "object"
#guard outcome (withSymbol [.strLit "k"]
  (.member (.call (.ident "Object") [s]) "description")) == "k"
#guard outcome (withSymbol [.strLit "k"] (.binary .strictEq
  (.call (.member (.call (.ident "Object") [s]) "valueOf") []) s)) == "true"

-- 20.4.1: `Symbol` has a `[[Construct]]`, and all it does is refuse.
#guard outcome (expr (.new (.ident "Symbol") []))
  == "uncaught: TypeError: Symbol is not a constructor"

/-! ## Symbol-keyed properties

They are in the one property list, so `delete`, `in`, and
`getOwnPropertyDescriptor` all reach them; they are invisible to every
operation the specification makes string-only. -/

#guard outcome (keyed (.index (.ident "o") s)) == "1"
#guard outcome (keyed (.binary .«in» s (.ident "o"))) == "true"
#guard outcome (keyed (.call (.member (.ident "o") "hasOwnProperty") [s])) == "true"
#guard outcome (keyed (.call (.member (.ident "o") "propertyIsEnumerable") [s])) == "true"
#guard outcome (keyed (.member (.call (.member (.ident "Object") "keys")
  [.ident "o"]) "length")) == "1"
#guard outcome (keyed (.member (.call (.member (.ident "Object") "getOwnPropertyNames")
  [.ident "o"]) "length")) == "1"
#guard outcome (keyed (.binary .strictEq
  (.index (.call (.member (.ident "Object") "getOwnPropertySymbols") [.ident "o"])
    (.numLit 0.0)) s)) == "true"
#guard outcome (keyed (.call (.member (.ident "JSON") "stringify") [.ident "o"]))
  == "{\"a\":0}"
#guard outcome (keyed (.binary .strictEq
  (.index (.call (.member (.ident "Object") "assign") [.objectLit [], .ident "o"]) s)
  (.numLit 1.0))) == "true"
#guard outcome (keyed (.delete (.index (.ident "o") s))) == "true"
#guard outcome (keyed (.member (.call (.member (.ident "Object") "getOwnPropertyDescriptor")
  [.ident "o", s]) "value")) == "1"

-- `for`-`in` is string-only: the symbol key is never visited.
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .varDecl .«const» [{ target := "o", init := some (.objectLit [.init "a" (.numLit 0.0)]) }],
    .exprStmt (.assign (.index (.ident "o") s) (.numLit 1.0)),
    .varDecl .«let» [{ target := "out", init := some (.strLit "") }],
    .forInStmt (.decl .«let» "k") (.ident "o")
      (.exprStmt (.assign (.ident "out") (.binary .add (.ident "out") (.ident "k")))),
    .exprStmt (.ident "out") ] == "a"

-- A computed key in an object literal takes ToPropertyKey, so a symbol
-- lands as a symbol key and `{ [s]: 1 }` is the literal form of what
-- `keyed` writes.
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .varDecl .«const»
      [{ target := "o",
         init := some (.objectLit [.init (.computed s) (.numLit 1.0), .init "a" (.numLit 0.0)]) }],
    .exprStmt (.index (.ident "o") s) ] == "1"
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .varDecl .«const»
      [{ target := "o",
         init := some (.objectLit [.init (.computed s) (.numLit 1.0), .init "a" (.numLit 0.0)]) }],
    .exprStmt (.call (.member (.ident "JSON") "stringify") [.ident "o"]) ] == "{\"a\":0}"

-- A symbol-keyed method's `name` is its key's description in brackets
-- (10.2.9).
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .varDecl .«const»
      [{ target := "o",
         init := some (.objectLit [.method .method (.computed s) [] []]) }],
    .exprStmt (.member (.index (.ident "o") s) "name") ] == "[k]"

-- A symbol with no description names the method the empty string, which
-- is 10.2.9 step 1.b and not `"[]"`.
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") []) }],
    .varDecl .«const»
      [{ target := "o",
         init := some (.objectLit [.init (.computed s) (.funcExpr none [] [])]) }],
    .exprStmt (.member (.index (.ident "o") s) "name") ] == ""

-- `Object.defineProperty` takes a symbol key like any other.
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
    .exprStmt (.call (.member (.ident "Object") "defineProperty")
      [.ident "o", s, .objectLit [.init "value" (.numLit 2.0)]]),
    .exprStmt (.index (.ident "o") s) ] == "2"

-- A message that names a symbol key prints its descriptive string.
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .exprStmt (.assign (.index (.numLit 1.0) s) (.numLit 1.0)) ]
  == "uncaught: TypeError: Cannot set properties of 1 (setting 'Symbol(k)')"

/-! ## `Obj.ownKeys` puts the symbols last

OrdinaryOwnPropertyKeys (10.1.11.1) in full, read off a hand-built
object: the indices in numeric order, then the other string keys in
insertion order, then the symbol keys in insertion order. -/

private def twoSymbols : Obj :=
  { properties :=
      [ (.sym { id := 0, description := some "x" }, Property.ordinary (.prim .undef)),
        ("b", Property.ordinary (.prim .undef)),
        ("1", Property.ordinary (.prim .undef)),
        (.sym { id := 1, description := some "y" }, Property.ordinary (.prim .undef)),
        ("0", Property.ordinary (.prim .undef)) ] }

#guard twoSymbols.ownKeys ==
  [ Key.str "0", Key.str "1", Key.str "b",
    Key.sym { id := 0, description := some "x" },
    Key.sym { id := 1, description := some "y" } ]
#guard twoSymbols.stringKeys == ["0", "1", "b"]
#guard twoSymbols.symbolKeys == [{ id := 0, description := some "x" },
                                 { id := 1, description := some "y" }]
#guard twoSymbols.enumerableKeys == ["0", "1", "b"]

/-! ## The thirteen well-known symbols -/

#guard WellKnownSymbol.all.length == 13
#guard (WellKnownSymbol.all.map (·.id)).eraseDups.length == 13
#guard WellKnownSymbol.iterator.description == "Symbol.iterator"

#guard WellKnownSymbol.all.all fun w =>
  outcome (expr (.unary .typeof (.member (.ident "Symbol") w.name))) == "symbol"
#guard outcome (expr (.member (.member (.ident "Symbol") "iterator") "description"))
  == "Symbol.iterator"

-- They have no attribute at all, so a write is the strict-mode refusal
-- an assignment to `Math.PI` is.
#guard outcome (expr (.assign (.member (.ident "Symbol") "iterator") (.numLit 1.0)))
  == "uncaught: TypeError: Cannot assign to read only property 'iterator' of object '#<Object>'"

/-! ## `@@toStringTag` -/

-- A method call binds `this` to the base, so this reads
-- `Object.prototype`'s own tag, which is no tag at all.
#guard outcome (expr (.call (.member (.member (.ident "Object") "prototype") "toString") []))
  == "[object Object]"
#guard outcome (expr (.call
  (.member (.member (.member (.ident "Object") "prototype") "toString") "call")
  [.ident "Math"])) == "[object Math]"
#guard outcome (expr (.call
  (.member (.member (.member (.ident "Object") "prototype") "toString") "call")
  [.ident "JSON"])) == "[object JSON]"
#guard outcome (expr (.call
  (.member (.member (.member (.ident "Object") "prototype") "toString") "call")
  [.call (.ident "Symbol") []])) == "[object Symbol]"
#guard outcome (expr (.call
  (.member (.member (.member (.ident "Object") "prototype") "toString") "call")
  [.objectLit []])) == "[object Object]"

-- A tag a script defines for itself.
#guard outcome
  [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
    .exprStmt (.call (.member (.ident "Object") "defineProperty")
      [ .ident "o", .member (.ident "Symbol") "toStringTag",
        .objectLit [.init "value" (.strLit "X")] ]),
    .exprStmt (.call
      (.member (.member (.member (.ident "Object") "prototype") "toString") "call")
      [.ident "o"]) ] == "[object X]"

/-! ## `@@toPrimitive`

The handler is called with the hint's name: `"default"` under `+`,
`"string"` under `String()`, and `"number"` under every other coercing
operator. -/

/-- `const o = {}; Object.defineProperty(o, Symbol.toPrimitive, { value: function (h) { return h; } });`
and then one expression. -/
private def withHandler (body : List Stmt) (e : Expr) : Program :=
  [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
    .exprStmt (.call (.member (.ident "Object") "defineProperty")
      [ .ident "o", .member (.ident "Symbol") "toPrimitive",
        .objectLit [.init "value" (.funcExpr none ["h"] body)] ]),
    .exprStmt e ]

/-- `function (h) { return h; }` -/
private def echoHint : List Stmt := [.returnStmt (some (.ident "h"))]

#guard outcome (withHandler echoHint (.binary .add (.ident "o") (.strLit ""))) == "default"
#guard outcome (withHandler echoHint (.call (.ident "String") [.ident "o"])) == "string"
-- Under `-` the hint is `"number"`, and `"number" - 0` is NaN.
#guard outcome (withHandler echoHint (.binary .sub (.ident "o") (.numLit 0.0))) == "NaN"
#guard outcome (withHandler echoHint
  (.binary .add (.strLit "") (.binary .sub (.ident "o") (.numLit 0.0)))) == "NaN"

-- A handler that answers an object is the specification's refusal.
#guard outcome (withHandler [.returnStmt (some (.objectLit []))]
  (.binary .add (.ident "o") (.strLit "")))
  == "uncaught: TypeError: Cannot convert object to primitive value"

-- `Symbol.prototype[@@toPrimitive]` ignores its hint and answers the
-- symbol, which is why a symbol survives ToPropertyKey.
#guard outcome
  [ .varDecl .«const» [{ target := "s", init := some (.call (.ident "Symbol") [.strLit "k"]) }],
    .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
    .exprStmt (.assign (.index (.ident "o") (.call (.ident "Object") [s])) (.numLit 1.0)),
    .exprStmt (.index (.ident "o") s) ] == "1"

/-! ## `@@hasInstance` -/

#guard outcome
  [ .funcDecl "F" [] [],
    .exprStmt (.call (.member (.ident "Object") "defineProperty")
      [ .ident "F", .member (.ident "Symbol") "hasInstance",
        .objectLit [.init "value" (.funcExpr none [] [.returnStmt (some (.boolLit true))])] ]),
    .exprStmt (.binary .instanceof (.numLit 1.0) (.ident "F")) ] == "true"

-- The intrinsic handler is reachable and is OrdinaryHasInstance.
#guard outcome
  [ .funcDecl "F" [] [],
    .exprStmt (.call
      (.member (.index (.member (.ident "Function") "prototype")
        (.member (.ident "Symbol") "hasInstance")) "call")
      [.ident "F", .new (.ident "F") []]) ] == "true"

-- An ordinary `instanceof` still answers what it did.
#guard outcome
  [ .funcDecl "F" [] [],
    .exprStmt (.binary .instanceof (.new (.ident "F") []) (.ident "F")) ] == "true"
#guard outcome (expr (.binary .instanceof (.numLit 1.0) (.objectLit [])))
  == "uncaught: TypeError: Right-hand side of 'instanceof' is not callable"
