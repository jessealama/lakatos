import Tarski.Eval
import Tarski.Format

/-! Spread and holes.

ArgumentListEvaluation (13.3.8.1) and ArrayAccumulation (13.2.4.1) are
the two list evaluations a spread appears in, and both *iterate* it:
`f(...xs)` and `[...xs]` go through `xs`'s own `@@iterator`, so replacing
it changes what they see, and a value with none is `is not iterable`. An
object literal's spread is not iteration at all but CopyDataProperties
(7.3.26), which is why `{ ...null }` is `{}` and `{ ...o }` copies
symbol keys too.

A hole is neither: ArrayAccumulation counts it and defines nothing, so
`[1, , 2]` has length 3 and no `"1"` key — and `[...[1, , 2]]` *does*
have one, iteration reading the hole as `undefined`. -/

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

/-- `Symbol.iterator` as a computed key. -/
private def iterKey : PropKey := .computed (.member (.ident "Symbol") "iterator")

/-- `{ [Symbol.iterator]() { let i = 0; return { next: () => ({ value: i,
done: i++ >= <n> }) }; } }`: the values `0 .. n-1`. -/
private def upTo (n : Float) : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .varDecl .«let» [{ target := "i", init := some (num 0.0) }],
          .returnStmt (some (.objectLit
            [ .init "next" (.arrow [] (.expr (.objectLit
                [ .init "value" (.ident "i"),
                  .init "done" (.binary .ge (.update .inc false (.ident "i")) (.numLit n)) ]))) ])) ] ]

/-! ## Spread in an argument list -/

-- `Math.max(...[1, 5, 2]);`
#guard outcome
    [ .exprStmt (.call (.member (.ident "Math") "max")
        [.spread (.arrayLit [num 1.0, num 5.0, num 2.0])]) ]
  == "5"

-- `f(...a, 3, ...b)` keeps source order, and `arguments.length` counts
-- what the spreads produced.
#guard outcome
    [ .funcDecl "f" [] [.returnStmt (some (.member (.ident "arguments") "length"))],
      .exprStmt (.call (.ident "f")
        [ .spread (.arrayLit [num 1.0, num 2.0]), num 3.0,
          .spread (.arrayLit [num 4.0]) ]) ]
  == "4"

-- The order itself, read off the `arguments` object.
#guard outcome
    [ .funcDecl "f" []
        [ .returnStmt (some (.binary .add
            (.binary .mul (.index (.ident "arguments") (num 2.0)) (num 10.0))
            (.index (.ident "arguments") (num 3.0)))) ],
      .exprStmt (.call (.ident "f")
        [ .spread (.arrayLit [num 1.0, num 2.0]), num 3.0,
          .spread (.arrayLit [num 4.0]) ]) ]
  == "34"

-- `new C(...args)` and `super(...args)`.
/-- `class A { constructor(x, y) { this.v = x + y; } }` -/
private def classA : ClassDef :=
  { name := some "A", superClass := none,
    elements :=
      [ .ctor ["x", "y"]
          [.exprStmt (.assign (.member .this "v") (.binary .add (.ident "x") (.ident "y")))] ] }

/-- `class B extends A { constructor(...r) { super(...r); } }` -/
private def classB : ClassDef :=
  { name := some "B", superClass := some (.ident "A"),
    elements :=
      [ .ctor [{ target := "r", default := none, rest := true }]
          [.exprStmt (.superCall [.spread (.ident "r")])] ] }

private def spreadClasses : List Stmt :=
  [.classDecl "A" classA, .classDecl "B" classB]

#guard outcome
    (spreadClasses ++
      [.exprStmt (.member (.new (.ident "A") [.spread (.arrayLit [num 1.0, num 2.0])]) "v")])
  == "3"
#guard outcome
    (spreadClasses ++
      [.exprStmt (.member (.new (.ident "B") [.spread (.arrayLit [num 4.0, num 5.0])]) "v")])
  == "9"

-- A spread argument goes through the *iterator*, so a value with none
-- refuses.
#guard outcome [.exprStmt (.call (.ident "Math") [.spread (.objectLit [])])]
  == "uncaught: TypeError: [object Object] is not iterable"

/-! ## Spread in an array literal -/

-- `[...xs, ...it]` over an array and a user iterator.
#guard outcome
    [ «let» "xs" (.arrayLit [num 1.0, num 2.0]),
      .exprStmt (.call (.member
        (.arrayLit [.spread (.ident "xs"), .spread (upTo 2.0)]) "join") []) ]
  == "1,2,0,1"

-- `[...arguments]` inside a function.
#guard outcome
    [ .funcDecl "f" []
        [.returnStmt (some (.member (.arrayLit [.spread (.ident "arguments")]) "length"))],
      .exprStmt (.call (.ident "f") [num 1.0, num 2.0, num 3.0]) ]
  == "3"

-- An array whose own `@@iterator` was replaced is spread through the
-- replacement, which is what makes a spread *iteration* and not an
-- array-like read.
/-- `function () { let i = 0; return { next: () => ({ value: 9, done:
i++ >= 1 }) }; }`, an `@@iterator` that ignores its receiver. -/
private def oneNine : Expr :=
  .funcExpr none []
    [ .varDecl .«let» [{ target := "i", init := some (num 0.0) }],
      .returnStmt (some (.objectLit
        [ .init "next" (.arrow [] (.expr (.objectLit
            [ .init "value" (num 9.0),
              .init "done" (.binary .ge (.update .inc false (.ident "i")) (num 1.0)) ]))) ])) ]

#guard outcome
    [ «let» "xs" (.arrayLit [num 1.0, num 2.0]),
      .exprStmt (.assign (.index (.ident "xs") (.member (.ident "Symbol") "iterator")) oneNine),
      .exprStmt (.call (.member (.arrayLit [.spread (.ident "xs")]) "join") []) ]
  == "9"

/-! ## Holes

A hole defines nothing, so the index is absent; iteration reads it as
`undefined`, so spreading a holey array *defines* it. -/

#guard outcome [.exprStmt (.member (.arrayLit [num 1.0, .hole, num 2.0]) "length")] == "3"
#guard outcome
    [ .exprStmt (.binary .«in» (.strLit "1") (.arrayLit [num 1.0, .hole, num 2.0])) ]
  == "false"
#guard outcome [.exprStmt (.member (.arrayLit [.hole]) "length")] == "1"
#guard outcome
    [ .exprStmt (.call (.member (.arrayLit [.spread (.arrayLit [num 1.0, .hole, num 2.0])])
        "hasOwnProperty") [.strLit "1"]) ]
  == "true"

/-! ## Spread in an object literal

CopyDataProperties, not iteration: own enumerable keys, string and symbol
both, *defined* on the literal. -/

#guard outcome
    [ «let» "s" (.call (.ident "Symbol") [.strLit "k"]),
      «let» "src" (.objectLit [.init "a" (num 1.0), .init (.computed (.ident "s")) (num 2.0)]),
      «let» "o" (.objectLit [.spread (.ident "src")]),
      .exprStmt (.binary .add (.member (.ident "o") "a") (.index (.ident "o") (.ident "s"))) ]
  == "3"

-- Inherited and non-enumerable keys are not copied.
#guard outcome
    [ «let» "parent" (.objectLit [.init "p" (num 1.0)]),
      «let» "src" (.objectLit [.proto (.ident "parent"), .init "q" (num 2.0)]),
      .exprStmt (.call (.member (.ident "Object") "defineProperty")
        [ .ident "src", .strLit "hidden",
          .objectLit [.init "value" (num 3.0), .init "enumerable" (.boolLit false)] ]),
      .exprStmt (.call (.member (.call (.member (.ident "Object") "keys")
        [.objectLit [.spread (.ident "src")]]) "join") []) ]
  == "q"

-- A getter on the source runs, once, and its *value* is what is copied.
#guard outcome
    [ .varDecl .«let» [{ target := "reads", init := some (num 0.0) }],
      «let» "src" (.objectLit [.method .getter "a" []
        [ .exprStmt (.compoundAssign .add (.ident "reads") (num 1.0)),
          .returnStmt (some (num 1.0)) ]]),
      «let» "o" (.objectLit [.spread (.ident "src")]),
      .exprStmt (.binary .add (.member (.ident "o") "a") (.ident "reads")) ]
  == "2"

-- A string source is its *index* properties, which is what makes
-- `{ ..."ab" }` two members.
#guard outcome
    [ .exprStmt (.call (.member (.call (.member (.ident "Object") "values")
        [.objectLit [.spread (.strLit "ab")]]) "join") []) ]
  == "a,b"

-- A nullish source copies nothing at all.
#guard outcome
    [ .exprStmt (.call (.member (.call (.member (.ident "Object") "keys")
        [.objectLit [.spread .nullLit, .spread .undefLit]]) "join") []) ]
  == ""

-- A member later in the literal wins, and a spread is a *definition*, so
-- a setter of that name on the literal is replaced rather than called.
#guard outcome
    [ .exprStmt (.member (.objectLit
        [.init "a" (num 1.0), .spread (.objectLit [.init "a" (num 2.0)])]) "a") ]
  == "2"
#guard outcome
    [ .exprStmt (.member (.objectLit
        [ .method .setter "a" ["v"] [.throwStmt (.strLit "no")],
          .spread (.objectLit [.init "a" (num 3.0)]) ]) "a") ]
  == "3"
