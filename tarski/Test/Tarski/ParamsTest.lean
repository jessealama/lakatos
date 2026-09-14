import Tarski.Eval
import Tarski.Format

/-! Parameter defaults, the scope they run in, and `Function.length`.

A default runs when the argument *is* `undefined`, not when it is
missing, and it runs in the parameter scope: every parameter's cell
exists before any initializer does, so a default may read a parameter to
its left and one to its right is in its temporal dead zone.

The scope is the subtle part. With no default the `var`s share the
parameters' cells (10.2.11 step 27); with one they get a scope of their
own whose cells start from the parameters' values (step 28), so a closure
a default made keeps the parameter's cell while the body's `var` moves a
different one. That is observable without `eval`, which is why it is
implemented rather than approximated.

`length` is ExpectedArgumentCount — the parameters before the first
default — as an own data property on every function and class
constructor. Its attributes are #389's, as `prototype`'s are, and so is
`name`. -/

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

/-- `function f(<params>) { <body> } f(<call>);` -/
private def callF (params : List Param) (body : List Stmt) (call : List Expr) : Program :=
  [ .funcDecl "f" params body, .exprStmt (.call (.ident "f") call) ]

/-- `<name> = <e>` as a parameter. -/
private def dflt (name : String) (e : Expr) : Param := { target := name, default := some e }

/-! ## When a default runs -/

private def aPlusOne : List Param := ["a", dflt "b" (.binary .add (.ident "a") (num 1.0))]

private def returnB : List Stmt := [.returnStmt (some (.ident "b"))]

-- `function f(a, b = a + 1) { return b; } f(1);` — the default reads the
-- parameter to its left.
#guard outcome (callF aPlusOne returnB [num 1.0]) == "2"

-- `f(1, 5);` — an argument that is present wins.
#guard outcome (callF aPlusOne returnB [num 1.0, num 5.0]) == "5"

-- `f(1, undefined);` — an explicit `undefined` runs the default.
#guard outcome (callF aPlusOne returnB [num 1.0, .undefLit]) == "2"

-- `f(1, null);` — `null` is not `undefined`, so it does not.
#guard outcome (callF aPlusOne returnB [num 1.0, .nullLit]) == "null"

-- `let n = 0; function f(a = n = n + 1, b = n = n + 10) { return n; } f(7);`
-- — only the second default runs, so `n` ends at 10 rather than 11, and
-- the two run left to right.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (num 0.0) }],
      .funcDecl "f"
        [ dflt "a" (.assign (.ident "n") (.binary .add (.ident "n") (num 1.0))),
          dflt "b" (.assign (.ident "n") (.binary .add (.ident "n") (num 10.0))) ]
        [.returnStmt (some (.ident "n"))],
      .exprStmt (.call (.ident "f") [num 7.0]) ]
  == "10"

/-! ## The parameters' own dead zone -/

-- `function f(a = b, b = 1) { return a; } f();` — `b`'s cell exists and
-- holds nothing, so reading it from `a`'s default is the dead zone.
#guard outcome (callF [dflt "a" (.ident "b"), dflt "b" (num 1.0)]
    [.returnStmt (some (.ident "a"))] [])
  == "uncaught: ReferenceError: Cannot access 'b' before initialization"

-- `function f(a = a) {} f();` — and a parameter is in its own.
#guard outcome (callF [dflt "a" (.ident "a")] [] [])
  == "uncaught: ReferenceError: Cannot access 'a' before initialization"

-- `function f(a = arguments.length) { return a; } f();` — `arguments` is
-- bound before the parameters, so a default may read it.
#guard outcome
    (callF [dflt "a" (.member (.ident "arguments") "length")]
      [.returnStmt (some (.ident "a"))] [])
  == "0"

-- `f(undefined, 1);` — two arguments, so `length` is 2 even though the
-- first one ran the default.
#guard outcome
    (callF [dflt "a" (.member (.ident "arguments") "length")]
      [.returnStmt (some (.ident "a"))] [.undefLit, num 1.0])
  == "2"

/-! ## The `var` scope a default creates

10.2.11 step 28: the body's `var`s get their own cells, copied from the
parameters', rather than sharing them. -/

-- `function f(g = () => a, a = 1) { var a = 2; return g() + ":" + a; } f();`
-- — the closure the default made kept the *parameter*'s cell, so it
-- still answers 1 while the body's `var a` has moved to 2.
#guard outcome
    (callF [dflt "g" (.arrow [] (.expr (.ident "a"))), dflt "a" (num 1.0)]
      [ .varDecl .«var» [{ target := "a", init := some (num 2.0) }],
        .returnStmt (some (.binary .add
          (.binary .add (.call (.ident "g") []) (.strLit ":")) (.ident "a"))) ]
      [])
  == "1:2"

-- `function f(a = 1) { var a; return a; } f();` — a `var` with no
-- initializer performs no operation, so the copy stands.
#guard outcome
    (callF [dflt "a" (num 1.0)]
      [.varDecl .«var» [{ target := "a", init := none }], .returnStmt (some (.ident "a"))] [])
  == "1"

-- `function f(a = 1) { var a = 3; return a; } f();` — and one with an
-- initializer writes the copy.
#guard outcome
    (callF [dflt "a" (num 1.0)]
      [ .varDecl .«var» [{ target := "a", init := some (num 3.0) }],
        .returnStmt (some (.ident "a")) ]
      [])
  == "3"

-- `let x = "outer"; function f(g = () => x) { let x = "inner"; return g(); } f();`
-- — the parameter scope is outside the body's, so the default's closure
-- never sees the body's `let`.
#guard outcome
    [ .varDecl .«let» [{ target := "x", init := some (.strLit "outer") }],
      .funcDecl "f" [dflt "g" (.arrow [] (.expr (.ident "x")))]
        [ .varDecl .«let» [{ target := "x", init := some (.strLit "inner") }],
          .returnStmt (some (.call (.ident "g") [])) ],
      .exprStmt (.call (.ident "f") []) ]
  == "outer"

/-! ## Every function form takes them -/

-- `((a = 2) => a)();`
#guard outcome [.exprStmt (.call (.arrow [dflt "a" (num 2.0)] (.expr (.ident "a"))) [])]
  == "2"

-- `class Point { x; constructor(x = 0) { this.x = x; } } new Point().x;`
-- — the first of the two defaulted constructors the thales emitter's
-- fixtures carry, transcribed.
#guard outcome
    [ .classDecl "Point"
        { name := some "Point", superClass := none,
          elements :=
            [ .field false (.«public» "x") none,
              .ctor [dflt "x" (num 0.0)]
                [.exprStmt (.assign (.member .this "x") (.ident "x"))] ] },
      .exprStmt (.member (.new (.ident "Point") []) "x") ]
  == "0"

-- `class Switch { on; constructor(n, on = false) { this.on = n > 0 || on; }
--                 level() { return this.on ? 1 : 0; } }
--  new Switch(0).level();`
-- — the second one.
#guard outcome
    [ .classDecl "Switch"
        { name := some "Switch", superClass := none,
          elements :=
            [ .field false (.«public» "on") none,
              .ctor ["n", dflt "on" (.boolLit false)]
                [ .exprStmt (.assign (.member .this "on")
                    (.logical .or (.binary .gt (.ident "n") (num 0.0)) (.ident "on"))) ],
              .method .method false "level" []
                [ .returnStmt (some (.cond (.member .this "on") (num 1.0) (num 0.0))) ] ] },
      .exprStmt (.call (.member (.new (.ident "Switch") [num 0.0]) "level") []) ]
  == "0"

/-! ## `length` -/

-- `(function (a, b) {}).length;`
#guard outcome [.exprStmt (.member (.funcExpr none ["a", "b"] []) "length")] == "2"

-- `(function (a, b = 1, c) {}).length;` — the count stops at the first
-- default, whatever follows it.
#guard outcome
    [.exprStmt (.member (.funcExpr none ["a", dflt "b" (num 1.0), "c"] []) "length")]
  == "1"

-- `(() => 1).length;`
#guard outcome [.exprStmt (.member (.arrow [] (.expr (num 1.0))) "length")] == "0"

-- `((a, b) => 1).length;`
#guard outcome [.exprStmt (.member (.arrow ["a", "b"] (.expr (num 1.0))) "length")] == "2"

private def classA (elements : List ClassElement) : Stmt :=
  .classDecl "A" { name := some "A", superClass := none, elements }

-- `class A { constructor(a, b) {} } A.length;`
#guard outcome [classA [.ctor ["a", "b"] []], .exprStmt (.member (.ident "A") "length")]
  == "2"

-- `class A {} A.length;` — an implicit constructor has no parameters.
#guard outcome [classA [], .exprStmt (.member (.ident "A") "length")] == "0"

-- `class A {} class B extends A {} B.length;` — nor does a derived
-- class's implicit constructor, whose spec form is `constructor(...args)`.
#guard outcome
    [ classA [],
      .classDecl "B"
        { name := some "B", superClass := some (.ident "A"), elements := [] },
      .exprStmt (.member (.ident "B") "length") ]
  == "0"

-- `class A { m(a) {} } A.prototype.m.length;` — a method has one too.
#guard outcome
    [ classA [.method .method false "m" ["a"] []],
      .exprStmt (.member (.member (.member (.ident "A") "prototype") "m") "length") ]
  == "1"

-- `class A { m(a) {} } Object.keys(A.prototype.m).join();` — nothing,
-- a function's `length` and `name` being non-enumerable. That they are
-- *own* properties is what `m.hasOwnProperty` answers, now that a
-- function reaches `Object.prototype` through `Function.prototype`.
#guard outcome
    [ classA [.method .method false "m" ["a"] []],
      .exprStmt (.call
        (.member
          (.call (.member (.ident "Object") "keys")
            [.member (.member (.ident "A") "prototype") "m"])
          "join")
        []) ]
  == ""

-- `class A { m(a) {} } A.prototype.m.hasOwnProperty("length");`
#guard outcome
    [ classA [.method .method false "m" ["a"] []],
      .exprStmt (.call
        (.member (.member (.member (.ident "A") "prototype") "m") "hasOwnProperty")
        [.strLit "length"]) ]
  == "true"
