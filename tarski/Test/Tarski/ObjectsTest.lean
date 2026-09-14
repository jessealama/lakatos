import Tarski.Eval
import Tarski.Format

/-! Objects: literals, property access, the prototype chain, `new`,
`typeof`, and ToPrimitive.

There are no property descriptors here, and `Object.prototype` carries
`hasOwnProperty` and nothing else (#380); the rest of its surface is
#389's. What this file pins is the shape the descriptors will be
added to — own data properties in insertion order, a single prototype
link, and a set that writes an own property rather than through the
chain. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- `const o = { a: 1 };`, the object every read below starts from. -/
private def declareO : Stmt :=
  .varDecl .«const» [{ target := "o", init := some (.objectLit [.init "a" (.numLit 1.0)]) }]

/-! ## Reading and writing own properties -/

-- `const o = { a: 1 }; o.a;`
#guard outcome [declareO, .exprStmt (.member (.ident "o") "a")] == "1"

-- `const o = { a: 1 }; o["a"];`
#guard outcome [declareO, .exprStmt (.index (.ident "o") (.strLit "a"))] == "1"

-- `const o = { a: 1 }; o.missing;`
#guard outcome [declareO, .exprStmt (.member (.ident "o") "missing")] == "undefined"

-- `const o = { a: 1 }; o.b = 2; o.b;`
#guard outcome
    [ declareO,
      .exprStmt (.assign (.member (.ident "o") "b") (.numLit 2.0)),
      .exprStmt (.member (.ident "o") "b") ]
  == "2"

-- `const o = {}; o[1] = "x"; o["1"];` — a numeric key is ToPropertyKey'd
-- to its string, so the two spellings name one property.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
      .exprStmt (.assign (.index (.ident "o") (.numLit 1.0)) (.strLit "x")),
      .exprStmt (.index (.ident "o") (.strLit "1")) ]
  == "x"

-- `const o = { a: 1 }; o.a = 2; o.a;` — a repeated key overwrites.
#guard outcome
    [ declareO,
      .exprStmt (.assign (.member (.ident "o") "a") (.numLit 2.0)),
      .exprStmt (.member (.ident "o") "a") ]
  == "2"

/-! ## The prototype chain -/

/-- `function P() {} P.prototype.k = 5;` — an ordinary function comes
with a `prototype` object, and `new` links instances to it. -/
private def declareP : List Stmt :=
  [ .funcDecl "P" [] [],
    .exprStmt (.assign (.member (.member (.ident "P") "prototype") "k") (.numLit 5.0)) ]

-- `… const p = new P(); p.k;`
#guard outcome
    (declareP ++
      [ .varDecl .«const» [{ target := "p", init := some (.new (.ident "P") []) }],
        .exprStmt (.member (.ident "p") "k") ])
  == "5"

-- `… const p = new P(); p.k = 6; p.k;` — an own property shadows the
-- prototype's.
#guard outcome
    (declareP ++
      [ .varDecl .«const» [{ target := "p", init := some (.new (.ident "P") []) }],
        .exprStmt (.assign (.member (.ident "p") "k") (.numLit 6.0)),
        .exprStmt (.member (.ident "p") "k") ])
  == "6"

-- `… const p = new P(); p.k = 6; const q = new P(); q.k;` — and the
-- write did not go through to the prototype, so a second instance still
-- reads 5.
#guard outcome
    (declareP ++
      [ .varDecl .«const» [{ target := "p", init := some (.new (.ident "P") []) }],
        .exprStmt (.assign (.member (.ident "p") "k") (.numLit 6.0)),
        .varDecl .«const» [{ target := "q", init := some (.new (.ident "P") []) }],
        .exprStmt (.member (.ident "q") "k") ])
  == "5"

-- `function F() {} F.prototype.constructor === F;`
#guard outcome
    [ .funcDecl "F" [] [],
      .exprStmt (.binary .strictEq
        (.member (.member (.ident "F") "prototype") "constructor") (.ident "F")) ]
  == "true"

/-! ## What `new` answers -/

-- `function F() {} F.prototype = 1; new F() instanceof Object;` —
-- GetPrototypeFromConstructor's fallback. When NewTarget's `prototype`
-- is not an object the instance is linked to `Object.prototype`, which
-- is the specification's default and what #384 changed it to; before
-- that the instance had a null prototype and this answered `false`.
-- `Object.getPrototypeOf` is #389's, so `instanceof` is how the link is
-- observed.
#guard outcome
    [ .funcDecl "F" [] [],
      .exprStmt (.assign (.member (.ident "F") "prototype") (.numLit 1.0)),
      .exprStmt (.binary .instanceof (.new (.ident "F") []) (.ident "Object")) ]
  == "true"

-- `function F() { this.x = 1; } new F().x;` — the instance, with the
-- constructor's writes on it.
#guard outcome
    [ .funcDecl "F" [] [.exprStmt (.assign (.member .this "x") (.numLit 1.0))],
      .exprStmt (.member (.new (.ident "F") []) "x") ]
  == "1"

-- `function F() { return { y: 2 }; } new F().y;` — an explicitly
-- returned object wins.
#guard outcome
    [ .funcDecl "F" [] [.returnStmt (some (.objectLit [.init "y" (.numLit 2.0)]))],
      .exprStmt (.member (.new (.ident "F") []) "y") ]
  == "2"

-- `function F() { this.x = 1; return 7; } new F().x;` — a returned
-- primitive is ignored.
#guard outcome
    [ .funcDecl "F" []
        [ .exprStmt (.assign (.member .this "x") (.numLit 1.0)),
          .returnStmt (some (.numLit 7.0)) ],
      .exprStmt (.member (.new (.ident "F") []) "x") ]
  == "1"

/-! ## Bases that are not objects -/

-- `undefined.x;`
#guard outcome [.exprStmt (.member .undefLit "x")] == "uncaught: TypeError: Cannot read properties of undefined (reading 'x')"

-- `null.x;`
#guard outcome [.exprStmt (.member .nullLit "x")] == "uncaught: TypeError: Cannot read properties of null (reading 'x')"

-- `(1).x;` — the read goes through `Number.prototype`, which has no `x`
-- and whose chain ends at `Object.prototype`, so the answer is
-- `undefined`; no wrapper is allocated on the way.
#guard outcome [.exprStmt (.member (.numLit 1.0) "x")] == "undefined"

-- `(1).x = 2;` — but a write to a primitive is a strict-mode TypeError.
#guard outcome
    [.exprStmt (.assign (.member (.numLit 1.0) "x") (.numLit 2.0))] == "uncaught: TypeError: Cannot set properties of 1 (setting 'x')"

/-! ## `typeof` over the value domain -/

#guard outcome [.exprStmt (.unary .typeof (.numLit 1.0))] == "number"
#guard outcome [.exprStmt (.unary .typeof (.strLit "s"))] == "string"
#guard outcome [.exprStmt (.unary .typeof (.boolLit true))] == "boolean"
#guard outcome [.exprStmt (.unary .typeof .undefLit)] == "undefined"
-- `typeof null` is `"object"`, which is the language's oldest bug.
#guard outcome [.exprStmt (.unary .typeof .nullLit)] == "object"
#guard outcome [.exprStmt (.unary .typeof (.objectLit []))] == "object"
#guard outcome [.exprStmt (.unary .typeof (.arrow [] (.expr (.numLit 1.0))))] == "function"

/-! ## ToPrimitive -/

-- `({}) + 1;` — OrdinaryToPrimitive finds `valueOf` on
-- `Object.prototype`, which answers the object itself, and then
-- `toString`, which answers the tag.
#guard outcome [.exprStmt (.binary .add (.objectLit []) (.numLit 1.0))] == "[object Object]1"

-- `const o = { valueOf: function () { return 3; } }; o + 1;` — a
-- user-defined `valueOf` already works.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit
        [.init "valueOf" (.funcExpr none [] [.returnStmt (some (.numLit 3.0))])]) }],
      .exprStmt (.binary .add (.ident "o") (.numLit 1.0)) ]
  == "4"

-- `const o = { valueOf: … }; o === o;` — `===` does not coerce, so the
-- `valueOf` never runs and identity is the answer.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit
        [.init "valueOf" (.funcExpr none [] [.returnStmt (some (.numLit 3.0))])]) }],
      .exprStmt (.binary .strictEq (.ident "o") (.ident "o")) ]
  == "true"

-- `({ a: 1 }) === ({ a: 1 });` — and two literals are two objects.
#guard outcome
    [ .exprStmt (.binary .strictEq
        (.objectLit [.init "a" (.numLit 1.0)]) (.objectLit [.init "a" (.numLit 1.0)])) ]
  == "false"
