import Tarski.Eval
import Tarski.Format

/-! `for`-`in`: EnumerateObjectProperties.

14.7.5.9's algorithm is informative rather than normative, and this is
the part of it every engine agrees on and every test262 test relies on:
each object's own string keys are snapshotted when that object is
reached, a key is visited only if it is **still** own and enumerable
when its turn comes, and every key already seen shadows the prototypes'.

`for`-`in` lands with the property protocol rather than with the loops
because the enumerability it reads is #389's; `harness/propertyHelper.js`
needs both it and `delete`, and without them every `verifyProperty` test
stays refused. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- `const <n> = <e>;` -/
private def «let» (n : String) (e : Expr) : Stmt :=
  .varDecl .«const» [{ name := n, init := some e }]

/-- `const seen = [];`, the array every ordering case collects into. -/
private def seen : Stmt := «let» "seen" (.arrayLit [])

/-- `seen.push(<e>);` -/
private def push (e : Expr) : Stmt :=
  .exprStmt (.call (.member (.ident "seen") "push") [e])

/-- `seen.join();` -/
private def joinSeen : Stmt := .exprStmt (.call (.member (.ident "seen") "join") [])

/-- `for (const k in <o>) seen.push(k);` then `seen.join()`. -/
private def collect (o : Expr) (setup : List Stmt := []) : Program :=
  seen :: setup ++
    [ .forInStmt (.decl .«const» "k") o (push (.ident "k")),
      joinSeen ]

/-- An object built by assignment, since a numeric key in an object
literal is #395's: `{ b: 1, 2: 1, a: 1, 1: 1 }`. -/
private def mixedKeys : List Stmt :=
  [ «let» "o" (.objectLit []),
    .exprStmt (.assign (.member (.ident "o") "b") (.numLit 1.0)),
    .exprStmt (.assign (.index (.ident "o") (.numLit 2.0)) (.numLit 1.0)),
    .exprStmt (.assign (.member (.ident "o") "a") (.numLit 1.0)),
    .exprStmt (.assign (.index (.ident "o") (.numLit 1.0)) (.numLit 1.0)) ]

/-! ## Order

OrdinaryOwnPropertyKeys at every level: index keys ascending, then the
rest in insertion order. -/

#guard outcome (collect (.ident "o") mixedKeys) == "1,2,b,a"
#guard outcome (collect (.arrayLit [.numLit 7.0])) == "0"

/-! ## Enumerability

A non-enumerable key is skipped, which is why a function and a class
prototype enumerate nothing and an array's `length` never appears. -/

#guard outcome (collect (.funcExpr (some "f") [] [])) == ""
#guard outcome (collect (.new (.ident "Error") [.strLit "m"])) == ""
#guard outcome (collect (.objectLit [])) == ""
#guard outcome
    (collect (.ident "o")
      [ «let» "o" (.objectLit [.init "a" (.numLit 1.0)]),
        .exprStmt (.call (.member (.ident "Object") "defineProperty")
          [.ident "o", .strLit "b", .objectLit [.init "value" (.numLit 2.0)]]) ])
  == "a"

/-! ## The prototype chain

Own keys first, then each prototype's, and a key already seen is not
visited again however many levels carry it. -/

#guard outcome
    (collect (.ident "o")
      [ «let» "p" (.objectLit [.init "p1" (.numLit 1.0)]),
        «let» "o" (.call (.member (.ident "Object") "create") [.ident "p"]),
        .exprStmt (.assign (.member (.ident "o") "o1") (.numLit 1.0)) ])
  == "o1,p1"

#guard outcome
    (collect (.ident "o")
      [ «let» "p" (.objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)]),
        «let» "o" (.call (.member (.ident "Object") "create") [.ident "p"]),
        .exprStmt (.assign (.member (.ident "o") "a") (.numLit 3.0)) ])
  == "a,b"

-- A key the *prototype* hides with a non-enumerable own property of the
-- same name is still shadowed: the key was seen, and seeing is what
-- shadows.
#guard outcome
    (collect (.ident "o")
      [ «let» "p" (.objectLit [.init "a" (.numLit 1.0)]),
        «let» "o" (.call (.member (.ident "Object") "create") [.ident "p"]),
        .exprStmt (.call (.member (.ident "Object") "defineProperty")
          [.ident "o", .strLit "a", .objectLit [.init "value" (.numLit 2.0)]]) ])
  == ""

/-! ## The body may change the object

A key deleted before its turn is skipped; a key added during the loop is
not visited, the list having been taken when the object was reached. -/

#guard outcome
    [ seen,
      «let» "o" (.objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)]),
      .forInStmt (.decl .«const» "k") (.ident "o")
        (.block [push (.ident "k"), .exprStmt (.delete (.member (.ident "o") "b"))]),
      joinSeen ]
  == "a"

#guard outcome
    [ seen,
      «let» "o" (.objectLit [.init "a" (.numLit 1.0)]),
      .forInStmt (.decl .«const» "k") (.ident "o")
        (.block [push (.ident "k"),
                 .exprStmt (.assign (.member (.ident "o") "z") (.numLit 1.0))]),
      joinSeen ]
  == "a"

/-! ## The head's four shapes

A `let` or `const` head gets a fresh cell per iteration, so two closures
the body makes see two bindings; a `var` head is hoisted and outlives
the loop; an assignment target is written once per key. -/

#guard outcome
    [ «let» "fs" (.arrayLit []),
      «let» "o" (.objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)]),
      .forInStmt (.decl .«const» "k") (.ident "o")
        (.exprStmt (.call (.member (.ident "fs") "push")
          [.arrow [] (.expr (.ident "k"))])),
      .exprStmt (.binary .add
        (.call (.index (.ident "fs") (.numLit 0.0)) [])
        (.call (.index (.ident "fs") (.numLit 1.0)) [])) ]
  == "ab"

#guard outcome
    [ .varDecl .«var» [{ name := "k", init := none }],
      .exprStmt (.unary .typeof (.ident "k")) ]
  == "undefined"
#guard outcome
    [ «let» "o" (.objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)]),
      .forInStmt (.decl .«var» "k") (.ident "o") .empty,
      .exprStmt (.ident "k") ]
  == "b"

#guard outcome
    [ .varDecl .«let» [{ name := "k", init := none }],
      «let» "o" (.objectLit [.init "a" (.numLit 1.0)]),
      .forInStmt (.target (.ident "k")) (.ident "o") .empty,
      .exprStmt (.ident "k") ]
  == "a"

#guard outcome
    [ «let» "t" (.objectLit []),
      «let» "o" (.objectLit [.init "a" (.numLit 1.0)]),
      .forInStmt (.target (.member (.ident "t") "p")) (.ident "o") .empty,
      .exprStmt (.member (.ident "t") "p") ]
  == "a"

-- The right operand of a `let` head is evaluated in a scope that already
-- holds the name, uninitialized: `for (let x in x)` is the dead zone.
#guard outcome
    [.forInStmt (.decl .«let» "x") (.ident "x") .empty]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

/-! ## A nullish or primitive right operand

`undefined` and `null` run the body not at all and complete
`undefined`; a string enumerates its index keys. -/

#guard outcome [.forInStmt (.decl .«const» "k") .nullLit (.exprStmt (.numLit 1.0))]
  == "undefined"
#guard outcome [.forInStmt (.decl .«const» "k") .undefLit (.exprStmt (.numLit 1.0))]
  == "undefined"
#guard outcome (collect (.strLit "ab")) == "0,1"
#guard outcome (collect (.numLit 1.0)) == ""

/-! ## As a breakable statement

`break`, `continue`, and a labelled `continue` from a loop inside the
body, and the completion value UpdateEmpty threads. -/

#guard outcome
    [ seen,
      «let» "o" (.objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)]),
      .forInStmt (.decl .«const» "k") (.ident "o")
        (.block [push (.ident "k"), .breakStmt none]),
      joinSeen ]
  == "a"

#guard outcome
    [ seen,
      «let» "o" (.objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)]),
      .forInStmt (.decl .«const» "k") (.ident "o")
        (.block [.ifStmt (.binary .strictEq (.ident "k") (.strLit "a"))
                   (.continueStmt none) none,
                 push (.ident "k")]),
      joinSeen ]
  == "b"

#guard outcome
    [ seen,
      «let» "o" (.objectLit [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0)]),
      .labeled "outer"
        (.forInStmt (.decl .«const» "k") (.ident "o")
          (.block [ .whileStmt (.boolLit true) (.continueStmt (some "outer")),
                    push (.ident "k") ])),
      joinSeen ]
  == ""

#guard outcome
    [.forInStmt (.decl .«const» "k") (.objectLit [.init "a" (.numLit 1.0)])
      (.exprStmt (.numLit 5.0))]
  == "5"
