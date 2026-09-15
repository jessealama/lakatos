import Tarski.Eval
import Tarski.Format

/-! `Object.fromEntries` and `Object.groupBy`: the two `Object` members
that consume an iterable.

Both are one walk each over the protocol built for `for`-`of`, and both
close the iterator when anything between two steps throws — a non-object
entry, a throwing getter, a callback that throws. `fromEntries` is
AddEntriesFromIterable (24.1.1.2) with `"0"` the key and `"1"` the value;
`groupBy` is GroupBy (7.3.35) with `property` keys, whose answer is
null-prototyped, so a group named `toString` is a group and not an
inherited method. -/

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

/-- `Object.fromEntries(<e>)`. -/
private def fromEntries (e : Expr) : Expr :=
  .call (.member (.ident "Object") "fromEntries") [e]

/-- `Object.groupBy(<items>, <cb>)`. -/
private def groupBy (items cb : Expr) : Expr :=
  .call (.member (.ident "Object") "groupBy") [items, cb]

/-- `<e>.join()`. -/
private def joined (e : Expr) : Expr := .call (.member e "join") []

/-- `Object.keys(<e>).join()`. -/
private def keysOf (e : Expr) : Expr :=
  joined (.call (.member (.ident "Object") "keys") [e])

/-- `Symbol.iterator` as a computed key. -/
private def iterKey : PropKey := .computed (.member (.ident "Symbol") "iterator")

/-- `[["a", 1], ["b", 2]]`. -/
private def pairs : Expr :=
  .arrayLit [.arrayLit [.strLit "a", num 1.0], .arrayLit [.strLit "b", num 2.0]]

/-! ## `Object.fromEntries` -/

#guard outcome [«let» "o" (fromEntries pairs), .exprStmt (keysOf (.ident "o"))] == "a,b"
#guard outcome
    [ «let» "o" (fromEntries pairs),
      .exprStmt (.binary .add (.member (.ident "o") "a") (.member (.ident "o") "b")) ]
  == "3"
#guard outcome
    [ «let» "o" (fromEntries pairs),
      .exprStmt (.binary .strictEq
        (.call (.member (.ident "Object") "getPrototypeOf") [.ident "o"])
        (.member (.ident "Object") "prototype")) ]
  == "true"

-- A round trip through `Object.entries`.
#guard outcome
    [ «let» "src" (.objectLit [.init "a" (num 1.0), .init "b" (num 2.0)]),
      .exprStmt (keysOf (fromEntries
        (.call (.member (.ident "Object") "entries") [.ident "src"]))) ]
  == "a,b"

-- The entries come off a *user* iterator as readily as off an array.
private def oneEntry : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .varDecl .«let» [{ target := "i", init := some (num 0.0) }],
          .returnStmt (some (.objectLit
            [ .init "next" (.arrow [] (.expr (.objectLit
                [ .init "value" (.arrayLit [.strLit "k", num 5.0]),
                  .init "done" (.binary .ge (.update .inc false (.ident "i")) (num 1.0)) ]))) ])) ] ]

#guard outcome [.exprStmt (.member (fromEntries oneEntry) "k")] == "5"

-- A key goes through ToPropertyKey, so a symbol and a number both work.
#guard outcome
    [ «let» "s" (.call (.ident "Symbol") [.strLit "k"]),
      «let» "o" (fromEntries (.arrayLit [.arrayLit [.ident "s", num 1.0]])),
      .exprStmt (.index (.ident "o") (.ident "s")) ]
  == "1"
#guard outcome
    [ .exprStmt (keysOf (fromEntries (.arrayLit [.arrayLit [num 1.0, num 2.0]]))) ]
  == "1"

-- A non-object entry is its own refusal, and it closes the iterator.
#guard outcome [.exprStmt (fromEntries (.arrayLit [num 1.0]))]
  == "uncaught: TypeError: Iterator value 1 is not an entry object"
#guard outcome [.exprStmt (fromEntries .undefLit)]
  == "uncaught: TypeError: Cannot convert undefined or null to object"
#guard outcome [.exprStmt (.member (.member (.ident "Object") "fromEntries") "length")] == "1"

/-! ## `Object.groupBy` -/

/-- `(x) => (x % 2 ? "odd" : "even")`. -/
private def parity : Expr :=
  .arrow ["x"] (.expr (.cond (.binary .rem (.ident "x") (num 2.0))
    (.strLit "odd") (.strLit "even")))

private def oneTwoThree : Expr := .arrayLit [num 1.0, num 2.0, num 3.0]

#guard outcome
    [ «let» "g" (groupBy oneTwoThree parity),
      .exprStmt (.binary .add (joined (.member (.ident "g") "odd"))
        (joined (.member (.ident "g") "even"))) ]
  == "1,32"

-- First-seen order, and a null-prototyped answer.
#guard outcome [.exprStmt (keysOf (groupBy oneTwoThree parity))] == "odd,even"
#guard outcome
    [ .exprStmt (.binary .strictEq
        (.call (.member (.ident "Object") "getPrototypeOf") [groupBy oneTwoThree parity])
        .nullLit) ]
  == "true"

-- The callback takes the value *and* the zero-based index.
#guard outcome
    [ .exprStmt (keysOf (groupBy (.arrayLit [.strLit "a", .strLit "b"])
        (.arrow ["v", "i"] (.expr (.ident "i"))))) ]
  == "0,1"

-- The key goes through ToPropertyKey.
#guard outcome
    [ .exprStmt (keysOf (groupBy oneTwoThree (.arrow ["x"] (.expr (.ident "x"))))) ]
  == "1,2,3"

-- The refusals, and the callback's own throw closing the iterator.
#guard outcome [.exprStmt (groupBy oneTwoThree (num 1.0))]
  == "uncaught: TypeError: not a function"
#guard outcome [.exprStmt (groupBy .nullLit parity)]
  == "uncaught: TypeError: Cannot convert undefined or null to object"
#guard outcome [.exprStmt (.member (.member (.ident "Object") "groupBy") "length")] == "2"

/-- An iterator of `1` that counts its closes. -/
private def countingOne : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .varDecl .«let» [{ target := "i", init := some (num 0.0) }],
          .returnStmt (some (.objectLit
            [ .init "next" (.arrow [] (.expr (.objectLit
                [ .init "value" (num 1.0),
                  .init "done" (.binary .ge (.update .inc false (.ident "i")) (num 3.0)) ]))),
              .method .method "return" []
                [ .exprStmt (.compoundAssign .add (.ident "closed") (num 1.0)),
                  .returnStmt (some (.objectLit [])) ] ])) ] ]

private def closedZero : Stmt :=
  .varDecl .«let» [{ target := "closed", init := some (num 0.0) }]

#guard outcome
    [ closedZero,
      .tryStmt [.exprStmt (fromEntries countingOne)]
        (some { param := some "e", body := [.exprStmt (.ident "closed")] }) none ]
  == "1"
#guard outcome
    [ closedZero,
      .tryStmt [.exprStmt (groupBy countingOne (.arrow ["x"] (.block [.throwStmt (num 1.0)])))]
        (some { param := some "e", body := [.exprStmt (.ident "closed")] }) none ]
  == "1"
