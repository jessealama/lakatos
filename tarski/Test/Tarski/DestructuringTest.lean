import Tarski.Eval
import Tarski.Format

/-! Destructuring: one walk for both pattern families.

14.3.3 (a binding pattern) and 13.15.5 (an assignment pattern) are the
same order — key, then target reference, then value, then default, then
write — and `bindPattern` is that order once, with `BindMode` deciding
whether a leaf ends a cell's dead zone or is a PutValue. What differs
between the two families is therefore only *when* a leaf's reference is
evaluated, and the two `ref,next` cases below are what pin it.

The other rule worth stating: an **array** pattern is the iteration
protocol, so it closes the iterator on every exit but exhaustion —
including a default that throws — while an **object** pattern is
RequireObjectCoercible and a series of GetV. -/

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

/-- `const <p> = <e>;` -/
private def bind (p : Pattern) (e : Expr) : Stmt :=
  .varDecl .«const» [{ target := p, init := some e }]

/-- One array-pattern element with no default. -/
private def el (p : Pattern) : Option PatternElem := some { target := p, default := none }

/-- One with a default. -/
private def elD (p : Pattern) (d : Expr) : Option PatternElem :=
  some { target := p, default := some d }

/-- A shorthand object-pattern property, `{ a }`. -/
private def prop (k : String) : PatternProp :=
  { key := .name k, target := k, default := none }

/-- `{ k: <p> }`. -/
private def propAs (k : String) (p : Pattern) : PatternProp :=
  { key := .name k, target := p, default := none }

/-- `{ k: <p> = <d> }`. -/
private def propD (k : String) (p : Pattern) (d : Expr) : PatternProp :=
  { key := .name k, target := p, default := some d }

/-- `Symbol.iterator` as a computed key. -/
private def iterKey : PropKey := .computed (.member (.ident "Symbol") "iterator")

/-! ## The issue's two declarations -/

-- `const [a, , ...rest] = [1, 2, 3, 4]; a + rest.length;`
#guard outcome
    [ bind (.array [el "a", none] (some "rest")) (.arrayLit [num 1.0, num 2.0, num 3.0, num 4.0]),
      .exprStmt (.binary .add (.ident "a") (.member (.ident "rest") "length")) ]
  == "3"

-- `const { p, q: { r } = { r: 9 }, ...o } = { p: 1, s: 2 }; p + r + o.s;`
#guard outcome
    [ bind
        (.object [prop "p", propD "q" (.object [prop "r"] none) (.objectLit [.init "r" (num 9.0)])]
          (some (.ident "o")))
        (.objectLit [.init "p" (num 1.0), .init "s" (num 2.0)]),
      .exprStmt (.binary .add (.binary .add (.ident "p") (.ident "r"))
        (.member (.ident "o") "s")) ]
  == "12"

/-! ## Defaults, holes, and nesting -/

-- A default runs on `undefined` and not on `null`.
#guard outcome
    [ bind (.array [elD "a" (num 5.0)] none) (.arrayLit [.undefLit]), .exprStmt (.ident "a") ]
  == "5"
#guard outcome
    [ bind (.array [elD "a" (num 5.0)] none) (.arrayLit [.nullLit]), .exprStmt (.ident "a") ]
  == "null"

-- An elision steps the iterator and binds nothing.
#guard outcome
    [ bind (.array [none, el "b"] none) (.arrayLit [num 1.0, num 2.0]), .exprStmt (.ident "b") ]
  == "2"

-- A rest may itself be a pattern.
#guard outcome
    [ bind (.array [] (some (.array [el "a", el "b"] none))) (.arrayLit [num 1.0, num 2.0]),
      .exprStmt (.binary .add (.ident "a") (.ident "b")) ]
  == "3"

-- A computed key and a numeric key both go through ToPropertyKey.
#guard outcome
    [ .varDecl .«const» [{ target := "k", init := some (.strLit "a") }],
      bind (.object [{ key := .computed (.ident "k"), target := "v", default := none }] none)
        (.objectLit [.init "a" (num 7.0)]),
      .exprStmt (.ident "v") ]
  == "7"
#guard outcome
    [ bind (.object [{ key := .computed (num 1.0), target := "v", default := none }] none)
        (.objectLit [.init "1" (num 8.0)]),
      .exprStmt (.ident "v") ]
  == "8"

/-! ## The object rest

CopyDataProperties with the listed keys excluded: own *enumerable* keys
only, string and symbol both, onto a fresh ordinary object. -/

/-- `const <n> = <e>;` -/
private def «let» (n : String) (e : Expr) : Stmt :=
  .varDecl .«const» [{ target := n, init := some e }]

private def symbolK : Expr := .call (.ident "Symbol") [.strLit "k"]

private def mixedSource : Expr :=
  .objectLit
    [ .init "a" (num 1.0), .init "b" (num 2.0), .init (.computed (.ident "s")) (num 3.0) ]

/-- `Object.keys(rest).join()`. -/
private def restKeys : Expr :=
  .call (.member (.call (.member (.ident "Object") "keys") [.ident "rest"]) "join") []

#guard outcome
    [ «let» "s" symbolK, «let» "src" mixedSource,
      bind (.object [prop "a"] (some (.ident "rest"))) (.ident "src"),
      .exprStmt (.binary .add restKeys (.index (.ident "rest") (.ident "s"))) ]
  == "b3"

-- An inherited key is not copied, and a non-enumerable one is not either.
private def inheritingSource : Expr :=
  .objectLit [.proto (.ident "parent"), .init "q" (num 2.0)]

private def hideOne : Stmt :=
  .exprStmt (.call (.member (.ident "Object") "defineProperty")
    [ .ident "src", .strLit "hidden",
      .objectLit [.init "value" (num 3.0), .init "enumerable" (.boolLit false)] ])

#guard outcome
    [ «let» "parent" (.objectLit [.init "p" (num 1.0)]), «let» "src" inheritingSource, hideOne,
      bind (.object [] (some (.ident "rest"))) (.ident "src"),
      .exprStmt restKeys ]
  == "q"

-- The rest object is ordinary: its prototype is `Object.prototype`.
#guard outcome
    [ bind (.object [] (some (.ident "rest"))) (.objectLit []),
      .exprStmt (.binary .strictEq
        (.call (.member (.ident "Object") "getPrototypeOf") [.ident "rest"])
        (.member (.ident "Object") "prototype")) ]
  == "true"

/-! ## `var` patterns

A `var`'s cells are hoisting's, so they hold `undefined` before the
declarator runs and the write is PutValue rather than an
initialization. -/

#guard outcome
    [ .funcDecl "f" []
        [ .exprStmt (.ident "a"),
          .varDecl .«var» [{ target := .array [el "a"] none,
                             init := some (.arrayLit [num 1.0]) }],
          .returnStmt (some (.ident "a")) ],
      .exprStmt (.call (.ident "f") []) ]
  == "1"

/-! ## The assignment form

Its value is the *right* operand's, whatever the pattern wrote, and its
leaves are PutValue: an identifier, a member, and a computed member
alike. -/

-- `[a, b] = [b, a]` swaps.
#guard outcome
    [ .varDecl .«let» [{ target := "a", init := some (num 1.0) },
                       { target := "b", init := some (num 2.0) }],
      .exprStmt (.assignPattern (.array [el "a", el "b"] none)
        (.arrayLit [.ident "b", .ident "a"])),
      .exprStmt (.binary .add (.binary .mul (.ident "a") (num 10.0)) (.ident "b")) ]
  == "21"

-- `({ a, b } = o)`.
#guard outcome
    [ .varDecl .«let» [{ target := "a", init := none }, { target := "b", init := none }],
      .exprStmt (.assignPattern (.object [prop "a", prop "b"] none)
        (.objectLit [.init "a" (num 3.0), .init "b" (num 4.0)])),
      .exprStmt (.binary .add (.ident "a") (.ident "b")) ]
  == "7"

-- Member and computed-member leaves.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) },
                         { target := "k", init := some (.strLit "q") }],
      .exprStmt (.assignPattern
        (.array [el (.target (.member (.ident "o") "p")),
                 el (.target (.index (.ident "o") (.ident "k")))] none)
        (.arrayLit [num 1.0, num 2.0])),
      .exprStmt (.binary .add (.member (.ident "o") "p") (.member (.ident "o") "q")) ]
  == "3"

-- The whole expression's value is the right operand.
#guard outcome
    [ .varDecl .«let» [{ target := "a", init := none }],
      .exprStmt (.member (.assignPattern (.array [el "a"] none) (.arrayLit [num 1.0]))
        "length") ]
  == "1"

/-! ## A leaf's reference comes before the value

13.15.5.5 evaluates an element's target reference *before* the iterator
is stepped, and 13.15.5.4 before GetV: both are observable when the
target's object expression has an effect. -/

/-- `log.push(<s>);` -/
private def logPush (t : String) : Stmt :=
  .exprStmt (.call (.member (.ident "log") "push") [.strLit t])

private def logging : List Stmt :=
  [ «let» "log" (.arrayLit []), «let» "o" (.objectLit []),
    .funcDecl "base" [] [logPush "ref", .returnStmt (some (.ident "o"))] ]

private def joinLog : Stmt :=
  .exprStmt (.call (.member (.ident "log") "join") [])

/-- `base().p` as a leaf: the reference has an effect to watch. -/
private def watchedLeaf : Pattern :=
  .target (.member (.call (.ident "base") []) "p")

/-- An iterable whose `next` logs. -/
private def loggingIterable : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .returnStmt (some (.objectLit
            [ .init "next" (.arrow [] (.block
                [ logPush "next",
                  .returnStmt (some (.objectLit
                    [.init "value" (num 1.0), .init "done" (.boolLit false)])) ])) ])) ] ]

/-- An object whose `a` getter logs. -/
private def loggingGetter : Expr :=
  .objectLit [.method .getter "a" [] [logPush "get", .returnStmt (some (num 1.0))]]

#guard outcome
    (logging ++
      [ «let» "src" loggingIterable,
        .exprStmt (.assignPattern (.array [el watchedLeaf] none) (.ident "src")),
        joinLog ])
  == "ref,next"

#guard outcome
    (logging ++
      [ «let» "src" loggingGetter,
        .exprStmt (.assignPattern (.object [propAs "a" watchedLeaf] none) (.ident "src")),
        joinLog ])
  == "ref,get"

/-! ## The refusals -/

#guard outcome [bind (.array [elD "a" (.ident "a")] none) (.arrayLit [])]
  == "uncaught: ReferenceError: Cannot access 'a' before initialization"
#guard outcome [bind (.array [el "a"] none) (num 1.0)]
  == "uncaught: TypeError: 1 is not iterable"
#guard outcome [bind (.object [prop "a"] none) .nullLit]
  == "uncaught: TypeError: Cannot destructure 'null' as it is null."
#guard outcome [bind (.object [prop "a"] none) .undefLit]
  == "uncaught: TypeError: Cannot destructure 'undefined' as it is undefined."

-- A primitive that is not nullish is destructured through its wrapper's
-- reads: `const { length } = "ab"` is 2.
#guard outcome [bind (.object [prop "length"] none) (.strLit "ab"), .exprStmt (.ident "length")]
  == "2"

/-! ## NamedEvaluation

A SingleNameBinding's default is named for the binding; a pattern's and a
member leaf's are not. -/

#guard outcome
    [ bind (.object [propD "f" "f" (.funcExpr none [] [])] none) (.objectLit []),
      .exprStmt (.member (.ident "f") "name") ]
  == "f"
#guard outcome
    [ bind (.array [elD "g" (.arrow [] (.expr (num 1.0)))] none) (.arrayLit []),
      .exprStmt (.member (.ident "g") "name") ]
  == "g"
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
      .exprStmt (.assignPattern
        (.array [elD (.target (.member (.ident "o") "p")) (.funcExpr none [] [])] none)
        (.arrayLit [])),
      .exprStmt (.member (.member (.ident "o") "p") "name") ]
  == ""
#guard outcome
    [ .varDecl .«let» [{ target := "h", init := none }],
      .exprStmt (.assignPattern
        (.object [propD "h" "h" (.classExpr { name := none, superClass := none, elements := [] })]
          none)
        (.objectLit [])),
      .exprStmt (.member (.ident "h") "name") ]
  == "h"

/-! ## What an array pattern closes

An element left over closes the iterator; exhaustion does not; a default
that throws does. -/

private def closedZero : Stmt :=
  .varDecl .«let» [{ target := "closed", init := some (num 0.0) }]

/-- `return() { closed = closed + 1; return {}; }`. -/
private def counting : PropDef :=
  .method .method "return" []
    [ .exprStmt (.compoundAssign .add (.ident "closed") (num 1.0)),
      .returnStmt (some (.objectLit [])) ]

/-- An iterator of `n` copies of `v` that counts its closes. -/
private def limitedOf (v : Expr) (n : Float) : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .varDecl .«let» [{ target := "i", init := some (num 0.0) }],
          .returnStmt (some (.objectLit
            [ .init "next" (.arrow [] (.expr (.objectLit
                [ .init "value" v,
                  .init "done" (.binary .ge (.update .inc false (.ident "i")) (.numLit n)) ]))),
              counting ])) ] ]

/-- An iterator of `n` ones that counts its closes. -/
private def limited (n : Float) : Expr := limitedOf (num 1.0) n

#guard outcome
    [ closedZero, bind (.array [el "a"] none) (limited 3.0), .exprStmt (.ident "closed") ]
  == "1"
#guard outcome
    [ closedZero, bind (.array [el "a", el "b"] none) (limited 1.0),
      .exprStmt (.ident "closed") ]
  == "0"
-- A default runs only on an `undefined` value, so the iterator here
-- yields one and is *not* exhausted when the default throws.
#guard outcome
    [ closedZero,
      .tryStmt [bind (.array [elD "a" (.call (.ident "nope") [])] none) (limitedOf .undefLit 3.0)]
        (some { param := some "e", body := [.exprStmt (.ident "closed")] }) none ]
  == "1"

/-! ## A `catch` parameter, a parameter list, and a loop head -/

-- `try { throw new TypeError("m"); } catch ({ message }) { message }`
#guard outcome
    [ .tryStmt [.throwStmt (.new (.ident "TypeError") [.strLit "m"])]
        (some { param := some (.object [prop "message"] none),
                body := [.exprStmt (.ident "message")] }) none ]
  == "m"

-- `function f({ a, b: [c] = [2] }, ...rest) { return a + c + rest.length; }`
private def patternParams : List Param :=
  [ { target := .object [prop "a", propD "b" (.array [el "c"] none) (.arrayLit [num 2.0])] none,
      default := none },
    { target := "rest", default := none, rest := true } ]

#guard outcome
    [ .funcDecl "f" patternParams
        [.returnStmt (some (.binary .add (.binary .add (.ident "a") (.ident "c"))
          (.member (.ident "rest") "length")))],
      .exprStmt (.call (.ident "f")
        [.objectLit [.init "a" (num 1.0)], num 3.0, num 4.0]) ]
  == "5"

-- ExpectedArgumentCount stops at a rest parameter, and a pattern with no
-- default still counts as one.
#guard outcome
    [ .funcDecl "f" patternParams [], .exprStmt (.member (.ident "f") "length") ]
  == "1"
#guard outcome
    [ .exprStmt (.member (.funcExpr none ["a", { target := "r", default := none, rest := true }] [])
        "length") ]
  == "1"
#guard outcome
    [ .exprStmt (.call (.arrow [{ target := "r", default := none, rest := true }]
        (.expr (.member (.ident "r") "length"))) [num 1.0, num 2.0]) ]
  == "2"

-- A rest parameter does not change `arguments`, and its array is a fresh
-- `Array` on every call.
#guard outcome
    [ .funcDecl "f" [{ target := "r", default := none, rest := true }]
        [.returnStmt (some (.member (.ident "arguments") "length"))],
      .exprStmt (.call (.ident "f") [num 1.0, num 2.0, num 3.0]) ]
  == "3"
#guard outcome
    [ .funcDecl "f" [{ target := "r", default := none, rest := true }]
        [.returnStmt (some (.binary .instanceof (.ident "r") (.ident "Array")))],
      .exprStmt (.call (.ident "f") []) ]
  == "true"

-- A method and a class constructor take a pattern parameter too.
#guard outcome
    [ .exprStmt (.call (.member (.objectLit
        [.method .method "m" [{ target := .object [prop "a"] none, default := none }]
          [.returnStmt (some (.ident "a"))]]) "m") [.objectLit [.init "a" (num 6.0)]]) ]
  == "6"
private def patternCtor : ClassDef :=
  { name := some "C", superClass := none,
    elements :=
      [ .ctor [{ target := .array [el "a"] none, default := none }]
          [.exprStmt (.assign (.member .this "v") (.ident "a"))] ] }

#guard outcome
    [ .classDecl "C" patternCtor,
      .exprStmt (.member (.new (.ident "C") [.arrayLit [num 9.0]]) "v") ]
  == "9"

-- 10.2.11 step 28: a parameter with an initializer gives the `var`s a
-- scope of their own whose cells start from the parameters' values.
#guard outcome
    [ .funcDecl "f" [{ target := .array [el "a"] none, default := some (.arrayLit [num 1.0]) }]
        [ .varDecl .«var» [{ target := "a", init := none }],
          .returnStmt (some (.ident "a")) ],
      .exprStmt (.call (.ident "f") []) ]
  == "1"

-- A pattern head, in each of the three loop forms.
#guard outcome
    [ .forOfStmt (.decl .«const» (.array [el "k", el "v"] none))
        (.call (.member (.ident "Object") "entries") [.objectLit [.init "a" (num 1.0)]])
        (.exprStmt (.binary .add (.ident "k") (.ident "v"))) ]
  == "a1"
#guard outcome
    [ .varDecl .«let» [{ target := "a", init := none }, { target := "b", init := none }],
      .forOfStmt (.pattern (.array [el "a", el "b"] none))
        (.arrayLit [.arrayLit [num 1.0, num 2.0]]) .empty,
      .exprStmt (.binary .add (.ident "a") (.ident "b")) ]
  == "3"
#guard outcome
    [ .varDecl .«let» [{ target := "x", init := none }],
      .forOfStmt (.pattern (.object [prop "x"] none))
        (.arrayLit [.objectLit [.init "x" (num 1.0)]]) .empty,
      .exprStmt (.ident "x") ]
  == "1"
-- A `for`-`in` head may be a pattern too, and each key is destructured
-- as an assignment pattern. An *array* pattern over a key is the string
-- iterator, which `String.prototype` does not have until #391, so this
-- pins the refusal rather than `"xy"`.
#guard outcome
    [ .varDecl .«let» [{ target := "a", init := none }, { target := "b", init := none }],
      .forInStmt (.pattern (.array [el "a", el "b"] none)) (.objectLit [.init "xy" (num 1.0)])
        .empty,
      .exprStmt (.binary .add (.ident "a") (.ident "b")) ]
  == "uncaught: TypeError: xy is not iterable"

-- An *object* pattern over a key reads through the string's properties,
-- which needs no iterator.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := none }],
      .forInStmt (.pattern (.object [propAs "length" "n"] none))
        (.objectLit [.init "xy" (num 1.0)]) .empty,
      .exprStmt (.ident "n") ]
  == "2"
