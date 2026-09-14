import Tarski.Eval
import Tarski.Format

/-! `JSON.parse` and `JSON.stringify` as a script sees them.

`Test/Tarski/JsonGrammarTest.lean` pins the text half — what is JSON and
what a refusal says — with no heap at all. This file is the other half:
the reviver's walk, the replacer, the gap, `toJSON`, the wrappers, and
the three number cases the issue names.

The number arm is the numeric slice's: a finite Number is
`Js.Number.toDecimalString`, which is why `-0` prints `0`, and NaN and
the infinities are `null`, JSON having no text for either. -/

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

/-- `JSON.stringify(<args>)`. -/
private def stringify (args : List Expr) : Expr :=
  .call (.member (.ident "JSON") "stringify") args

/-- `JSON.parse(<args>)`. -/
private def parse (args : List Expr) : Expr :=
  .call (.member (.ident "JSON") "parse") args

/-- `{ a: [1, { b: null }] }`, the issue's object. -/
private def nested : Expr :=
  .objectLit [.init "a" (.arrayLit [.numLit 1.0, .objectLit [.init "b" (.nullLit)]])]

/-! ## `JSON` itself -/

#guard outcome (expr (.unary .typeof (.ident "JSON"))) == "object"
#guard outcome (expr (.call (.ident "JSON") [])) == "uncaught: TypeError: not a function"

/-! ## The three number cases, and the cycle -/

#guard outcome (expr (stringify [.unary .neg (.numLit 0.0)])) == "0"
#guard outcome (expr (stringify [.numLit 0.0])) == "0"
#guard outcome (expr (stringify [.ident "NaN"])) == "null"
#guard outcome (expr (stringify [.ident "Infinity"])) == "null"
#guard outcome (expr (stringify [.unary .neg (.ident "Infinity")])) == "null"
#guard outcome (expr (stringify [.numLit 1.5])) == "1.5"

#guard outcome
  [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
    .exprStmt (.assign (.member (.ident "o") "self") (.ident "o")),
    .exprStmt (stringify [.ident "o"]) ]
  == "uncaught: TypeError: Converting circular structure to JSON"

-- A repeated *sibling* is not a cycle: the stack holds the path, not
-- everything already seen.
#guard outcome
  [ .varDecl .«const» [{ name := "x", init := some (.objectLit []) }],
    .exprStmt (stringify [.arrayLit [.ident "x", .ident "x"]]) ] == "[{},{}]"

/-! ## What has no JSON text -/

#guard outcome (expr (stringify [.undefLit])) == "undefined"
#guard outcome (expr (stringify [.call (.ident "Symbol") []])) == "undefined"
#guard outcome (expr (stringify [.funcExpr none [] []])) == "undefined"
#guard outcome (expr (stringify [.objectLit [.init "x" (.undefLit)]])) == "{}"
#guard outcome (expr (stringify [.arrayLit [.undefLit, .funcExpr none [] []]]))
  == "[null,null]"
#guard outcome (expr (stringify [.objectLit []])) == "{}"

-- A BigInt is a `TypeError` rather than a text. No expression in this
-- AST builds one, so the refusal is stated against the serializer
-- directly.
#guard match (serializeJsonValue {} [] "" (.prim (.bigint 1))).run.run Heap.initial with
  | some (.error (.throw v), h) => describeThrown h v
      == "TypeError: Do not know how to serialize a BigInt"
  | _ => false

/-! ## Strings, booleans, and `null` -/

#guard outcome (expr (stringify [.strLit "a\"b"])) == "\"a\\\"b\""
#guard outcome (expr (stringify [.boolLit true])) == "true"
#guard outcome (expr (stringify [.nullLit])) == "null"
#guard outcome (expr (stringify [nested])) == "{\"a\":[1,{\"b\":null}]}"

/-! ## Wrappers, `toJSON`, and a getter -/

#guard outcome (expr (stringify [.new (.ident "Number") [.numLit 2.0]])) == "2"
#guard outcome (expr (stringify [.new (.ident "Boolean") [.boolLit false]])) == "false"

#guard outcome
  [ .varDecl .«const»
      [{ name := "o",
         init := some (.objectLit
           [.init "toJSON" (.funcExpr none ["k"] [.returnStmt (some (.ident "k"))])]) }],
    .exprStmt (stringify [.objectLit [.init "x" (.ident "o")]]) ] == "{\"x\":\"x\"}"

#guard outcome
  [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
    .exprStmt (.call (.member (.ident "Object") "defineProperty")
      [ .ident "o", .strLit "x",
        .objectLit [.init "get" (.funcExpr none [] [.returnStmt (some (.numLit 7.0))]), .init "enumerable" (.boolLit true)] ]),
    .exprStmt (stringify [.ident "o"]) ] == "{\"x\":7}"

/-! ## The replacer -/

#guard outcome (expr (stringify
  [ .objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)],
    .funcExpr none ["k", "v"]
      [ .ifStmt (.binary .strictEq (.ident "k") (.strLit "b"))
          (.returnStmt (some .undefLit)) none,
        .returnStmt (some (.ident "v")) ] ])) == "{\"a\":1}"

-- An array replacer is a PropertyList: strings and Numbers, the
-- duplicates dropped and the first occurrence's place kept.
#guard outcome (expr (stringify
  [ .objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0), .init "1" (.numLit 3.0)],
    .arrayLit [.strLit "b", .strLit "a", .strLit "b", .numLit 1.0] ]))
  == "{\"b\":2,\"a\":1,\"1\":3}"

#guard outcome (expr (stringify
  [ .objectLit [.init "a" (.numLit 1.0)],
    .arrayLit [.new (.ident "Number") [.numLit 0.0], .strLit "a"] ])) == "{\"a\":1}"

/-! ## The gap -/

#guard outcome (expr (stringify [nested, .nullLit, .numLit 2.0]))
  == "{\n  \"a\": [\n    1,\n    {\n      \"b\": null\n    }\n  ]\n}"
#guard outcome (expr (stringify [.objectLit [.init "a" (.numLit 1.0)], .nullLit, .numLit 12.0]))
  == "{\n          \"a\": 1\n}"
#guard outcome (expr (stringify [.objectLit [.init "a" (.numLit 1.0)], .nullLit, .strLit "ab"]))
  == "{\nab\"a\": 1\n}"
#guard outcome (expr (stringify
  [.objectLit [.init "a" (.numLit 1.0)], .nullLit, .strLit "0123456789ab"]))
  == "{\n0123456789\"a\": 1\n}"
#guard outcome (expr (stringify [.objectLit [.init "a" (.numLit 1.0)], .nullLit, .boolLit true]))
  == "{\"a\":1}"
#guard outcome (expr (stringify [.arrayLit [], .nullLit, .numLit 2.0])) == "[]"
#guard outcome (expr (stringify [.objectLit [], .nullLit, .numLit 2.0])) == "{}"

/-! ## `JSON.parse` -/

#guard outcome (expr (.index (.member (parse [.strLit "{\"x\":[1,2]}"]) "x") (.numLit 1.0)))
  == "2"
#guard outcome (expr (parse [.strLit " \t\n\r1 "])) == "1"
#guard outcome (expr (parse [.strLit "\"a\""])) == "a"
#guard outcome (expr (.call (.member (.ident "Object") "is")
  [parse [.strLit "-0"], .unary .neg (.numLit 0.0)])) == "true"
#guard outcome (expr (parse [.strLit "01"]))
  == "uncaught: SyntaxError: Unexpected token in JSON at position 1"
#guard outcome (expr (parse [.strLit ""]))
  == "uncaught: SyntaxError: Unexpected end of JSON input"

-- A duplicate key is the last one, and `__proto__` is an own property
-- rather than a prototype change: every member is a *definition*.
#guard outcome (expr (parse [.strLit "{\"a\":1,\"a\":2}", .undefLit])) == "[object Object]"
#guard outcome (expr (.member (parse [.strLit "{\"a\":1,\"a\":2}"]) "a")) == "2"
#guard outcome (expr (.call (.member (parse [.strLit "{\"__proto__\":1}"]) "hasOwnProperty")
  [.strLit "__proto__"])) == "true"

/-! ## The reviver -/

#guard outcome (expr (.member (parse
  [ .strLit "{\"a\":1}",
    .funcExpr none ["k", "v"]
      [ .ifStmt (.binary .strictEq (.ident "k") (.strLit "a"))
          (.returnStmt (some (.numLit 9.0))) none,
        .returnStmt (some (.ident "v")) ] ]) "a")) == "9"

#guard outcome (expr (.call (.member (parse
  [ .strLit "{\"a\":1,\"b\":2}",
    .funcExpr none ["k", "v"]
      [ .ifStmt (.binary .strictEq (.ident "k") (.strLit "a"))
          (.returnStmt (some .undefLit)) none,
        .returnStmt (some (.ident "v")) ] ]) "hasOwnProperty") [.strLit "a"])) == "false"

-- The walk is depth first and the root comes last, under the key `""`.
#guard outcome
  [ .varDecl .«let» [{ name := "seen", init := some (.strLit "") }],
    .exprStmt (parse
      [ .strLit "{\"a\":{\"b\":1}}",
        .funcExpr none ["k", "v"]
          [ .exprStmt (.assign (.ident "seen")
              (.binary .add (.binary .add (.ident "seen") (.ident "k")) (.strLit "|"))),
            .returnStmt (some (.ident "v")) ] ]),
    .exprStmt (.ident "seen") ] == "b|a||"

-- An array's elements are walked by its length, in index order.
#guard outcome
  [ .varDecl .«let» [{ name := "seen", init := some (.strLit "") }],
    .exprStmt (parse
      [ .strLit "[10,20]",
        .funcExpr none ["k", "v"]
          [ .exprStmt (.assign (.ident "seen")
              (.binary .add (.binary .add (.ident "seen") (.ident "k")) (.strLit "|"))),
            .returnStmt (some (.ident "v")) ] ]),
    .exprStmt (.ident "seen") ] == "0|1||"

/-! ## A round trip -/

#guard outcome (expr (stringify [parse [.strLit "{\"a\":[1,{\"b\":null}]}"]]))
  == "{\"a\":[1,{\"b\":null}]}"
