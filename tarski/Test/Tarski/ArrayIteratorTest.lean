import Tarski.Eval
import Tarski.Format

/-! The Array Iterator: `keys`, `values`, `entries`, and `@@iterator`.

23.1.5.1's three slots are `ObjKind.arrayIterator`, so the iterator's
state is fields and not properties: nothing enumerates it and no write
can forge one. `[[IteratedArrayLike]]` becomes `undefined` when the walk
runs out, which is what keeps an exhausted iterator done even after the
array grows; the length is read *every* step, which is what makes an
array that grows mid-walk visit the new elements.

The three methods take ToObject of their receiver (23.1.3.19 step 1), so
an array-like works and `Array.prototype.values.call(undefined)` is the
ToObject refusal. `Array.prototype[@@iterator]` is
`Array.prototype.values` itself — one object, not two — and an
`arguments` object's `@@iterator` is that same object. The tag is what
makes `[object Array Iterator]`: there is no `builtinTag` row for an
iterator. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

private def num (x : Float) : Expr := .numLit x

/-- `const <n> = <e>;` -/
private def «let» (n : String) (e : Expr) : Stmt :=
  .varDecl .«const» [{ target := n, init := some e }]

/-- `[1, 2]`. -/
private def twelve : Expr := .arrayLit [num 1.0, num 2.0]

/-- `Array.prototype`. -/
private def arrayProto : Expr := .member (.ident "Array") "prototype"

/-- `Object.getPrototypeOf(<e>)`. -/
private def protoOf (e : Expr) : Expr :=
  .call (.member (.ident "Object") "getPrototypeOf") [e]

/-- `Object.prototype.toString.call(<e>)`. -/
private def tagOf (e : Expr) : Expr :=
  .call (.member (.member (.member (.ident "Object") "prototype") "toString") "call") [e]

/-- `<e>.join()`. -/
private def joined (e : Expr) : Expr := .call (.member e "join") []

/-! ## What the three answer -/

-- `for (const k of [1, 2].keys()) …` — the indices.
#guard outcome
    [ «let» "out" (.arrayLit []),
      .forOfStmt (.decl .«const» "k") (.call (.member twelve "keys") [])
        (.exprStmt (.call (.member (.ident "out") "push") [.ident "k"])),
      .exprStmt (joined (.ident "out")) ]
  == "0,1"

-- `values` and `@@iterator` are the same walk, and the same function.
#guard outcome
    [ .exprStmt (joined (.arrayLit [.spread (.call (.member twelve "values") [])])) ]
  == "1,2"
#guard outcome
    [ .exprStmt (.binary .strictEq
        (.index arrayProto (.member (.ident "Symbol") "iterator"))
        (.member arrayProto "values")) ]
  == "true"

-- `entries` answers a fresh two-element array per step.
#guard outcome
    [ «let» "out" (.arrayLit []),
      .forOfStmt (.decl .«const» "e") (.call (.member twelve "entries") [])
        (.exprStmt (.call (.member (.ident "out") "push") [joined (.ident "e")])),
      .exprStmt (joined (.ident "out")) ]
  == "0,1,1,2"

-- A step's result is CreateIterResultObject: `value` then `done`, both
-- ordinary data properties.
#guard outcome
    [ «let» "it" (.call (.member twelve "keys") []),
      «let» "r" (.call (.member (.ident "it") "next") []),
      .exprStmt (joined (.call (.member (.ident "Object") "keys") [.ident "r"])) ]
  == "value,done"
#guard outcome
    [ «let» "it" (.call (.member twelve "keys") []),
      «let» "r" (.call (.member (.ident "it") "next") []),
      .exprStmt (joined (.arrayLit
        [.member (.ident "r") "value", .member (.ident "r") "done"])) ]
  == "0,false"

/-! ## The two prototypes

`%ArrayIteratorPrototype%` has `next` and the tag; its own prototype is
`%IteratorPrototype%`, whose `@@iterator` answers its receiver — which is
what makes an array iterator itself iterable. Neither has a name in
source: `Object.getPrototypeOf` is the only way to either. -/

#guard outcome
    [ .exprStmt (.binary .strictEq
        (.member (protoOf (.call (.member twelve "values") [])) "next")
        (.member (protoOf (.call (.member twelve "keys") [])) "next")) ]
  == "true"
#guard outcome
    [ .exprStmt (.index (protoOf (.call (.member twelve "values") []))
        (.member (.ident "Symbol") "toStringTag")) ]
  == "Array Iterator"
#guard outcome [.exprStmt (tagOf (.call (.member twelve "values") []))]
  == "[object Array Iterator]"
#guard outcome
    [ .exprStmt (.binary .strictEq (protoOf (protoOf (.call (.member twelve "values") [])))
        (protoOf (protoOf (.call (.member twelve "keys") [])))) ]
  == "true"
#guard outcome
    [ .exprStmt (.binary .strictEq
        (protoOf (protoOf (protoOf (.call (.member twelve "values") []))))
        (.member (.ident "Object") "prototype")) ]
  == "true"

-- An array iterator is itself iterable, through `%IteratorPrototype%`.
#guard outcome
    [ «let» "it" (.call (.member twelve "values") []),
      .exprStmt (.binary .strictEq
        (.call (.index (.ident "it") (.member (.ident "Symbol") "iterator")) [])
        (.ident "it")) ]
  == "true"
#guard outcome
    [ .exprStmt (joined (.arrayLit [.spread (.call (.member twelve "values") [])])) ]
  == "1,2"

/-! ## The state, and what reads it -/

-- An exhausted iterator stays done, whatever the array does next.
#guard outcome
    [ «let» "xs" (.arrayLit [num 1.0]),
      «let» "it" (.call (.member (.ident "xs") "values") []),
      .exprStmt (.call (.member (.ident "it") "next") []),
      .exprStmt (.call (.member (.ident "it") "next") []),
      .exprStmt (.call (.member (.ident "xs") "push") [num 2.0]),
      .exprStmt (.member (.call (.member (.ident "it") "next") []) "done") ]
  == "true"

-- An array that grows *before* the walk runs out is visited: the length
-- is read every step.
#guard outcome
    [ «let» "xs" (.arrayLit [num 1.0]),
      «let» "it" (.call (.member (.ident "xs") "values") []),
      .exprStmt (.call (.member (.ident "it") "next") []),
      .exprStmt (.call (.member (.ident "xs") "push") [num 2.0]),
      .exprStmt (.member (.call (.member (.ident "it") "next") []) "value") ]
  == "2"

-- ToObject, so an array-like walks and a nullish receiver refuses.
#guard outcome
    [ «let» "like" (.objectLit
        [.init "length" (num 2.0), .init "0" (.strLit "a"), .init "1" (.strLit "b")]),
      .exprStmt (joined (.arrayLit
        [.spread (.call (.member (.member arrayProto "values") "call") [.ident "like"])])) ]
  == "a,b"
#guard outcome
    [ .exprStmt (.call (.member (.member arrayProto "values") "call") [.undefLit]) ]
  == "uncaught: TypeError: Cannot convert undefined or null to object"

-- `next` off anything that is not an array iterator.
#guard outcome
    [ .exprStmt (.call (.member (.member (protoOf (.call (.member twelve "values") [])) "next")
        "call") [.objectLit []]) ]
  == "uncaught: TypeError: next method called on incompatible receiver [object Object]"

/-! ## 17.1's shape on the new functions -/

#guard outcome [.exprStmt (.member (.member arrayProto "entries") "length")] == "0"
#guard outcome [.exprStmt (.member (.member arrayProto "keys") "name")] == "keys"
#guard outcome
    [ «let» "it" (.call (.member twelve "values") []),
      .exprStmt (.binary .add (.member (.member (.ident "it") "next") "length")
        (.member (.member (.ident "it") "next") "name")) ]
  == "0next"

/-! ## `arguments`

10.4.4.6 step 8 links an `arguments` object's `@@iterator` to
`%Array.prototype.values%` itself, as a writable, non-enumerable,
configurable method. -/

#guard outcome
    [ .funcDecl "f" []
        [ .returnStmt (some (.binary .strictEq
            (.index (.ident "arguments") (.member (.ident "Symbol") "iterator"))
            (.member arrayProto "values"))) ],
      .exprStmt (.call (.ident "f") []) ]
  == "true"
#guard outcome
    [ .funcDecl "f" []
        [ .returnStmt (some (joined (.arrayLit [.spread (.ident "arguments")]))) ],
      .exprStmt (.call (.ident "f") [num 1.0, num 2.0]) ]
  == "1,2"
#guard outcome
    [ .funcDecl "f" []
        [ «let» "d" (.call (.member (.ident "Object") "getOwnPropertyDescriptor")
            [.ident "arguments", .member (.ident "Symbol") "iterator"]),
          .returnStmt (some (joined (.arrayLit
            [ .member (.ident "d") "writable", .member (.ident "d") "enumerable",
              .member (.ident "d") "configurable" ]))) ],
      .exprStmt (.call (.ident "f") []) ]
  == "true,false,true"
