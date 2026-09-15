import Tarski.Eval
import Tarski.Format

/-! The iteration protocol, on iterators a program wrote itself.

GetIterator, IteratorStepValue, and IteratorClose (7.4.3, 7.4.8, 7.4.11)
are three definitions, and what they do is visible only through an
iterator whose `next` and `return` a test can watch. That is what this
file does: every iterable here is an object literal with a
`[Symbol.iterator]` method, so each case says exactly which methods ran
and in which order.

The rule the whole file turns on: **a throw that comes from the iterator
closes nothing**. A `next` that throws, a `done` getter that throws, and
a `value` getter that throws each escape with no `return` called, because
7.4.8 sets `[[Done]]` before it rethrows. Everything else that leaves a
`for`-`of` early — a `break`, a `return`, a `continue` this loop does not
answer for, a body that throws — calls `return`.

`Test/Tarski/ForOfUnfoldTest.lean` is the other side of the loop: this
file runs whole programs, that one unfolds one iteration at a time. -/

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

/-- `Symbol.iterator` as a computed key. -/
private def iterKey : PropKey := .computed (.member (.ident "Symbol") "iterator")

/-- `{ [Symbol.iterator]() { return { <members> }; } }`: an iterable
whose iterator object is written out member by member. -/
private def iterable (members : List PropDef) : Expr :=
  .objectLit [.method .method iterKey [] [.returnStmt (some (.objectLit members))]]

/-- `next: () => ({ value: <v>, done: <done> })`. -/
private def nextOf (v done : Expr) : PropDef :=
  .init "next" (.arrow [] (.expr (.objectLit [.init "value" v, .init "done" done])))

/-- `return() { closed = closed + 1; return {}; }` — the close every
`closed`-counting case watches. -/
private def counting : PropDef :=
  .method .method "return" []
    [ .exprStmt (.compoundAssign .add (.ident "closed") (num 1.0)),
      .returnStmt (some (.objectLit [])) ]

/-- `let closed = 0;` -/
private def closedZero : Stmt := .varDecl .«let» [{ target := "closed", init := some (num 0.0) }]

/-- `const it = <e>;` -/
private def itIs (e : Expr) : Stmt := .varDecl .«const» [{ target := "it", init := some e }]

/-- `for (const v of it) <body>` -/
private def forOfIt (body : Stmt) : Stmt :=
  .forOfStmt (.decl .«const» "v") (.ident "it") body

/-- An iterator that never runs out and counts its closes. Every case
using it leaves the loop on its first or second iteration. -/
private def endless : Expr := iterable [nextOf (num 1.0) (.boolLit false), counting]

/-- An iterator of `n` ones that counts its closes. -/
private def twice (n : Float) : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .varDecl .«let» [{ target := "i", init := some (num 0.0) }],
          .returnStmt (some (.objectLit
            [ nextOf (num 1.0) (.binary .ge (.update .inc false (.ident "i")) (.numLit n)),
              counting ])) ] ]

/-- `closed;` -/
private def readClosed : Stmt := .exprStmt (.ident "closed")

/-! ## The issue's own example

`const it = { [Symbol.iterator]() { let i = 0; return { next: () => ({
value: i, done: i++ >= 3 }) }; } };` summed by a `for`-`of` is 3: the
member order is the source's, so `value` is read before `done` steps the
counter. -/

private def counter : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .varDecl .«let» [{ target := "i", init := some (num 0.0) }],
          .returnStmt (some (.objectLit
            [nextOf (.ident "i") (.binary .ge (.update .inc false (.ident "i")) (num 3.0))])) ] ]

#guard outcome
    [ itIs counter,
      .varDecl .«let» [{ target := "sum", init := some (num 0.0) }],
      forOfIt (.exprStmt (.compoundAssign .add (.ident "sum") (.ident "v"))),
      .exprStmt (.ident "sum") ]
  == "3"

/-! ## `return` on an abrupt exit

The issue's second acceptance criterion: a `break` out of a `for`-`of`
calls the iterator's `return`. So does a body that throws, a `return`
from the function around the loop, a labelled `break` through two loops —
each loop closes its own — and a `continue` naming a loop outside this
one. A `continue` this loop answers for closes nothing, because the loop
has not ended. -/

-- `for (const v of it) break; closed;`
#guard outcome [closedZero, itIs endless, forOfIt (.breakStmt none), readClosed] == "1"

-- A body that throws closes, and the body's own throw is what reports.
#guard outcome
    [ closedZero, itIs endless,
      .tryStmt [forOfIt (.throwStmt (.strLit "x"))]
        (some { param := some "e", body := [readClosed] }) none ]
  == "1"

-- `function f() { for (const v of it) return 7; } f(); closed;`
#guard outcome
    [ closedZero, itIs endless,
      .funcDecl "f" [] [forOfIt (.returnStmt (some (num 7.0)))],
      .exprStmt (.call (.ident "f") []),
      readClosed ]
  == "1"

-- A labelled `break` out of two `for`-`of`s closes both.
#guard outcome
    [ closedZero, itIs endless,
      .labeled "a" (forOfIt (forOfIt (.breakStmt (some "a")))),
      readClosed ]
  == "2"

-- A `continue` this loop answers for closes nothing: the loop runs on to
-- exhaustion, which is the one exit that calls no `return`.
#guard outcome
    [ closedZero, itIs (twice 2.0), forOfIt (.continueStmt none), readClosed ]
  == "0"

-- A `continue` naming a loop *outside* this one is abrupt here, so this
-- loop closes before it leaves; the outer loop runs twice, so the inner
-- iterator is closed twice.
#guard outcome
    [ closedZero,
      .labeled "a" (.forOfStmt (.decl .«const» "u") (.arrayLit [num 1.0, num 2.0])
        (.block [itIs endless, forOfIt (.continueStmt (some "a"))])),
      readClosed ]
  == "2"

/-! ## What does *not* close

A throw from `next` is the iterator's own, so no `return` runs (7.4.8
sets `[[Done]]` before rethrowing), and the throw reports. -/

private def throwingNext : PropDef :=
  .init "next" (.arrow [] (.block [.throwStmt (.strLit "boom")]))

#guard outcome
    [ closedZero, itIs (iterable [throwingNext, counting]),
      .tryStmt [forOfIt .empty] (some { param := some "e", body := [readClosed] }) none ]
  == "0"

-- Exhaustion is the other exit that closes nothing: `return` is called
-- only when the loop leaves *early*.
#guard outcome
    [ closedZero,
      itIs (iterable [nextOf (num 1.0) (.boolLit true), counting]),
      forOfIt .empty, readClosed ]
  == "0"

-- An iterator with no `return` at all is nothing to call: the `break`
-- simply leaves.
#guard outcome
    [ itIs (iterable [nextOf (num 1.0) (.boolLit false)]),
      forOfIt (.breakStmt none), .exprStmt (num 5.0) ]
  == "5"

/-! ## What `return` may answer

7.4.11 checks the answer is an object — but only when the completion
being carried out is *not* a throw, in which case every outcome of the
call is discarded and the original throw reaches the caller. -/

private def primitiveReturn : PropDef :=
  .method .method "return" [] [.returnStmt (some (num 1.0))]

private def withPrimitiveReturn : Expr :=
  iterable [nextOf (num 1.0) (.boolLit false), primitiveReturn]

-- A `break` is a normal completion, so the answer is checked.
#guard outcome [itIs withPrimitiveReturn, forOfIt (.breakStmt none)]
  == "uncaught: TypeError: Iterator result 1 is not an object"

-- A body throw discards it, and the body's error is what reports.
#guard outcome [itIs withPrimitiveReturn, forOfIt (.throwStmt (.strLit "mine"))]
  == "uncaught: mine"

/-! ## GetIterator's refusals -/

#guard outcome [.forOfStmt (.decl .«const» "x") (num 1.0) .empty]
  == "uncaught: TypeError: 1 is not iterable"
#guard outcome [.forOfStmt (.decl .«const» "x") (.objectLit []) .empty]
  == "uncaught: TypeError: [object Object] is not iterable"
#guard outcome [.forOfStmt (.decl .«const» "x") .nullLit .empty]
  == "uncaught: TypeError: null is not iterable"
#guard outcome [.forOfStmt (.decl .«const» "x") .undefLit .empty]
  == "uncaught: TypeError: undefined is not iterable"

-- A non-callable `@@iterator` is not iterable either.
#guard outcome
    [ .forOfStmt (.decl .«const» "x") (.objectLit [.init iterKey (num 1.0)]) .empty ]
  == "uncaught: TypeError: [object Object] is not iterable"

-- An `@@iterator` that answers a primitive has its own row.
#guard outcome
    [ .forOfStmt (.decl .«const» "x")
        (.objectLit [.method .method iterKey [] [.returnStmt (some (num 1.0))]]) .empty ]
  == "uncaught: TypeError: Result of the Symbol.iterator method is not an object"

-- And so does a `next` that answers one.
#guard outcome
    [ .forOfStmt (.decl .«const» "x")
        (iterable [.init "next" (.arrow [] (.expr (num 1.0)))]) .empty ]
  == "uncaught: TypeError: Iterator result 1 is not an object"

/-! ## `next` is read once

GetIterator reads `next` off the iterator object and keeps it, so a
getter that counts its reads answers 1 however many steps the loop
takes. -/

#guard outcome
    [ .varDecl .«let» [{ target := "reads", init := some (num 0.0) }],
      itIs (.objectLit
        [ .method .method iterKey []
            [ .returnStmt (some (.objectLit
                [ .method .getter "next" []
                    [ .exprStmt (.compoundAssign .add (.ident "reads") (num 1.0)),
                      .returnStmt (some (.arrow []
                        (.expr (.objectLit
                          [ .init "value" (num 1.0),
                            .init "done" (.binary .ge (.ident "reads") (num 9.0)) ])))) ] ])) ] ]),
      forOfIt (.breakStmt none),
      .exprStmt (.ident "reads") ]
  == "1"

/-! ## The head, the bindings, and the completion value -/

-- The head's own scope is a dead zone while the right operand runs.
#guard outcome [.forOfStmt (.decl .«let» "x") (.ident "x") .empty]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

-- A `let` head gets a fresh cell per iteration, so two closures the body
-- made read two values.
#guard outcome
    [ .varDecl .«const» [{ target := "fs", init := some (.arrayLit []) }],
      .forOfStmt (.decl .«let» "x") (.arrayLit [num 1.0, num 2.0])
        (.exprStmt (.call (.member (.ident "fs") "push")
          [.arrow [] (.expr (.ident "x"))])),
      .exprStmt (.binary .add
        (.call (.index (.ident "fs") (num 0.0)) [])
        (.call (.index (.ident "fs") (num 1.0)) [])) ]
  == "3"

-- A `var` head writes the binding hoisting already made, so it outlives
-- the loop.
#guard outcome
    [ .forOfStmt (.decl .«var» "x") (.arrayLit [num 1.0, num 2.0]) .empty,
      .exprStmt (.ident "x") ]
  == "2"

-- A member head is written once per value.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
      .forOfStmt (.target (.member (.ident "o") "p")) (.arrayLit [num 1.0]) .empty,
      .exprStmt (.member (.ident "o") "p") ]
  == "1"

-- The loop's completion value is what the body left, and a body that
-- never runs still completes `undefined`. A `break` out of an `if`
-- carries that `if`'s own running value, which is `undefined` — the same
-- answer `for` gives for the same program, this being `evalStmt`'s
-- threading rather than anything the loop does.
#guard outcome
    [ .forOfStmt (.decl .«const» "k") (.arrayLit [num 1.0, num 2.0, num 3.0])
        (.block
          [ .ifStmt (.binary .strictEq (.ident "k") (num 2.0)) (.breakStmt none) none,
            .exprStmt (.ident "k") ]) ]
  == "undefined"
#guard outcome
    [ .forOfStmt (.decl .«const» "k") (.arrayLit [num 1.0, num 2.0]) (.exprStmt (.ident "k")) ]
  == "2"
#guard outcome [.forOfStmt (.decl .«const» "k") (.arrayLit []) (.exprStmt (num 9.0))]
  == "undefined"

-- `done` is read through ToBoolean, so `done: 0` keeps going.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (num 0.0) }],
      itIs (.objectLit
        [ .method .method iterKey []
            [ .returnStmt (some (.objectLit
                [ nextOf (num 1.0)
                    (.cond (.binary .ge (.ident "n") (num 2.0)) (.strLit "yes") (num 0.0)) ])) ] ]),
      forOfIt (.exprStmt (.compoundAssign .add (.ident "n") (num 1.0))),
      .exprStmt (.ident "n") ]
  == "2"
