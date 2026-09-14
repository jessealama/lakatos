import Tarski.Eval
import Tarski.Format

/-! `throw`, `try`/`catch`/`finally`, and the `Error` hierarchy.

Three things are pinned. The completion-record semantics of `try`: a
`catch` replaces a *throw* and nothing else, a normal `finally` leaves the
try's completion standing while keeping its own writes, and an abrupt
`finally` overrides — `try { return 1; } finally { return 2; }` is 2. The
realm: seven constructors, each with its prototype, `name`, `message`,
and `constructor`, linked so that a subclass instance is an `Error`. And
the evaluator's own refusals, which are now catchable objects of the
right class carrying the message `Tarski/Eval.lean`'s table fixes.

Every expectation is what an engine prints for the same source. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout —
`uncaught: …` being what follows `Uncaught ` on stderr. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- `try { <block> } catch (<param>) { <body> }`, the common shape. -/
private def tryCatch (block : List Stmt) (param : Option String) (body : List Stmt) : Stmt :=
  .tryStmt block (some { param, body }) none

/-- A one-expression statement list. -/
private def stmt (e : Expr) : List Stmt := [.exprStmt e]

/-! ## The issue's example

```js
function inv(x) { if (x === 0) throw new RangeError("zero"); return 1 / x; }
let caught = "";
try { inv(0); }
catch (e) { caught = e instanceof RangeError ? e.message : "wrong"; }
finally { caught = caught + "!"; }
caught;
```
-/

#guard outcome
    [ .funcDecl "inv" ["x"]
        [ .ifStmt (.binary .strictEq (.ident "x") (.numLit 0.0))
            (.throwStmt (.new (.ident "RangeError") [.strLit "zero"])) none,
          .returnStmt (some (.binary .div (.numLit 1.0) (.ident "x"))) ],
      .varDecl .«let» [{ target := "caught", init := some (.strLit "") }],
      .tryStmt (stmt (.call (.ident "inv") [.numLit 0.0]))
        (some { param := some "e",
                body := stmt (.assign (.ident "caught")
                  (.cond (.binary .instanceof (.ident "e") (.ident "RangeError"))
                    (.member (.ident "e") "message") (.strLit "wrong"))) })
        (some (stmt (.assign (.ident "caught")
          (.binary .add (.ident "caught") (.strLit "!"))))),
      .exprStmt (.ident "caught") ]
  == "zero!"

/-! ## What a script can throw

Any value, not only an Error; the report falls back to the printed
form. -/

-- `throw 1;`
#guard outcome [.throwStmt (.numLit 1.0)] == "uncaught: 1"

-- `throw "x";`
#guard outcome [.throwStmt (.strLit "x")] == "uncaught: x"

-- `throw {};`
#guard outcome [.throwStmt (.objectLit [])] == "uncaught: [object Object]"

/-! ## The evaluator's own refusals, caught

Each is an instance of the class the table says, carrying the message the
table says. -/

-- `try { undeclared; } catch (e) { e instanceof ReferenceError; }`
#guard outcome
    [tryCatch (stmt (.ident "undeclared")) (some "e")
      (stmt (.binary .instanceof (.ident "e") (.ident "ReferenceError")))]
  == "true"

-- `try { null.x; } catch (e) { e instanceof TypeError && e.name === "TypeError"; }`
#guard outcome
    [tryCatch (stmt (.member .nullLit "x")) (some "e")
      (stmt (.logical .and
        (.binary .instanceof (.ident "e") (.ident "TypeError"))
        (.binary .strictEq (.member (.ident "e") "name") (.strLit "TypeError"))))]
  == "true"

-- `try { x; } catch (e) { e.message; } let x;` — the dead zone names the
-- binding it could not reach.
#guard outcome
    [ tryCatch (stmt (.ident "x")) (some "e") (stmt (.member (.ident "e") "message")),
      .varDecl .«let» [{ target := "x", init := none }] ]
  == "Cannot access 'x' before initialization"

-- `const c = 1; try { c = 2; } catch (e) { e instanceof TypeError; }`
#guard outcome
    [ .varDecl .«const» [{ target := "c", init := some (.numLit 1.0) }],
      tryCatch (stmt (.assign (.ident "c") (.numLit 2.0))) (some "e")
        (stmt (.binary .instanceof (.ident "e") (.ident "TypeError"))) ]
  == "true"

-- `try { (1)(); } catch (e) { e.message; }` — the issue's second example
-- fixes this text.
#guard outcome
    [tryCatch (stmt (.call (.numLit 1.0) [])) (some "e")
      (stmt (.member (.ident "e") "message"))]
  == "not a function"

/-! ## The Error hierarchy -/

-- `new Error("m").message;`
#guard outcome [.exprStmt (.member (.new (.ident "Error") [.strLit "m"]) "message")] == "m"

-- `new Error().message;` — the empty string, inherited from the
-- prototype, since no argument was given.
#guard outcome [.exprStmt (.member (.new (.ident "Error") []) "message")] == ""

-- `Error("m") instanceof Error;` — called as a function, an Error
-- constructor constructs.
#guard outcome
    [.exprStmt (.binary .instanceof (.call (.ident "Error") [.strLit "m"]) (.ident "Error"))]
  == "true"

-- `new TypeError("t") instanceof Error;` — the prototype link between a
-- subclass and `Error`.
#guard outcome
    [.exprStmt (.binary .instanceof (.new (.ident "TypeError") [.strLit "t"]) (.ident "Error"))]
  == "true"

-- `new Error() instanceof TypeError;` — and it does not run the other
-- way.
#guard outcome
    [.exprStmt (.binary .instanceof (.new (.ident "Error") []) (.ident "TypeError"))]
  == "false"

-- `new RangeError("zero").name;`
#guard outcome
    [.exprStmt (.member (.new (.ident "RangeError") [.strLit "zero"]) "name")]
  == "RangeError"

-- `new RangeError("zero").constructor === RangeError;`
#guard outcome
    [.exprStmt (.binary .strictEq
      (.member (.new (.ident "RangeError") [.strLit "zero"]) "constructor")
      (.ident "RangeError"))]
  == "true"

-- `new RangeError("zero").toString();`
#guard outcome
    [.exprStmt (.call (.member (.new (.ident "RangeError") [.strLit "zero"]) "toString") [])]
  == "RangeError: zero"

-- `new Error("").toString();` — an empty message leaves the name alone.
#guard outcome
    [.exprStmt (.call (.member (.new (.ident "Error") [.strLit ""]) "toString") [])]
  == "Error"

-- `TypeError.prototype instanceof Error;` — the intrinsics' own chain.
#guard outcome
    [.exprStmt (.binary .instanceof (.member (.ident "TypeError") "prototype") (.ident "Error"))]
  == "true"

-- `typeof Error;`
#guard outcome [.exprStmt (.unary .typeof (.ident "Error"))] == "function"

/-! ## What a `catch` does and does not do -/

-- `const o = {}; try { o.x = 1; throw 0; } catch {} o.x;` — the heap
-- survives a caught throw, which is what the monad's transformer order
-- is for.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
      tryCatch
        [.exprStmt (.assign (.member (.ident "o") "x") (.numLit 1.0)), .throwStmt (.numLit 0.0)]
        none [],
      .exprStmt (.member (.ident "o") "x") ]
  == "1"

-- `try { throw 1; } catch (e) { e = 2; e; }` — the binding is mutable.
#guard outcome
    [tryCatch [.throwStmt (.numLit 1.0)] (some "e")
      [.exprStmt (.assign (.ident "e") (.numLit 2.0)), .exprStmt (.ident "e")]]
  == "2"

-- `let e = "outer"; try { throw "inner"; } catch (e) {} e;` — and it
-- lives in a scope of its own.
#guard outcome
    [ .varDecl .«let» [{ target := "e", init := some (.strLit "outer") }],
      tryCatch [.throwStmt (.strLit "inner")] (some "e") [],
      .exprStmt (.ident "e") ]
  == "outer"

-- `function g() { throw new RangeError("r"); } try { g(); } catch (e) { e.name; }`
-- — a throw propagates out of a call.
#guard outcome
    [ .funcDecl "g" [] [.throwStmt (.new (.ident "RangeError") [.strLit "r"])],
      tryCatch (stmt (.call (.ident "g") [])) (some "e")
        (stmt (.member (.ident "e") "name")) ]
  == "RangeError"

/-! ## `finally`

A normal finalizer keeps its writes and leaves the try's completion
standing; an abrupt one overrides. -/

-- `function f() { try { return 1; } finally { return 2; } } f();`
#guard outcome
    [ .funcDecl "f" []
        [.tryStmt [.returnStmt (some (.numLit 1.0))] none
          (some [.returnStmt (some (.numLit 2.0))])],
      .exprStmt (.call (.ident "f") []) ]
  == "2"

-- `function f() { try { throw 1; } finally { return 2; } } f();`
#guard outcome
    [ .funcDecl "f" []
        [.tryStmt [.throwStmt (.numLit 1.0)] none (some [.returnStmt (some (.numLit 2.0))])],
      .exprStmt (.call (.ident "f") []) ]
  == "2"

-- `let n = 0; function f() { try { return 1; } finally { n = 5; } } f() + n;`
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (.numLit 0.0) }],
      .funcDecl "f" []
        [.tryStmt [.returnStmt (some (.numLit 1.0))] none
          (some (stmt (.assign (.ident "n") (.numLit 5.0))))],
      .exprStmt (.binary .add (.call (.ident "f") []) (.ident "n")) ]
  == "6"

-- `try { throw 1; } finally { }` — no handler, so the throw goes on.
#guard outcome [.tryStmt [.throwStmt (.numLit 1.0)] none (some [])] == "uncaught: 1"

-- `try { throw 1; } catch (e) { throw 2; } finally { }` — a handler that
-- throws is not caught by its own clause.
#guard outcome
    [.tryStmt [.throwStmt (.numLit 1.0)]
      (some { param := some "e", body := [.throwStmt (.numLit 2.0)] }) (some [])]
  == "uncaught: 2"

-- `try { try { throw 1; } finally { } } catch (e) { e; }`
#guard outcome
    [tryCatch [.tryStmt [.throwStmt (.numLit 1.0)] none (some [])] (some "e")
      (stmt (.ident "e"))]
  == "1"

/-! ## What a `try` completes with -/

-- `1; try { } catch {}` — the block starts from `undefined`, as `if`
-- does, so the 1 does not stand.
#guard outcome [.exprStmt (.numLit 1.0), tryCatch [] none []] == "undefined"

-- `try { 2; } finally { 3; }` — a normal finalizer's value is discarded.
#guard outcome
    [.tryStmt (stmt (.numLit 2.0)) none (some (stmt (.numLit 3.0)))] == "2"

-- `1; try { throw 0; } catch {}` — the handler's, likewise from
-- `undefined`.
#guard outcome
    [.exprStmt (.numLit 1.0), tryCatch [.throwStmt (.numLit 0.0)] none []] == "undefined"

/-! ## `instanceof` -/

-- `({}) instanceof 1;`
#guard outcome [.exprStmt (.binary .instanceof (.objectLit []) (.numLit 1.0))]
  == "uncaught: TypeError: Right-hand side of 'instanceof' is not callable"

-- `1 instanceof Error;` — a primitive left operand is not an instance of
-- anything, and says so rather than throwing.
#guard outcome [.exprStmt (.binary .instanceof (.numLit 1.0) (.ident "Error"))] == "false"

-- `function P() {} new P() instanceof P;`
#guard outcome
    [ .funcDecl "P" [] [],
      .exprStmt (.binary .instanceof (.new (.ident "P") []) (.ident "P")) ]
  == "true"

-- `({}) instanceof Error;`
#guard outcome [.exprStmt (.binary .instanceof (.objectLit []) (.ident "Error"))] == "false"

-- `const F = function () {}; F.prototype = 1; ({}) instanceof F;`
#guard outcome
    [ .varDecl .«const» [{ target := "F", init := some (.funcExpr none [] []) }],
      .exprStmt (.assign (.member (.ident "F") "prototype") (.numLit 1.0)),
      .exprStmt (.binary .instanceof (.objectLit []) (.ident "F")) ]
  == "uncaught: TypeError: Function has non-object prototype in instanceof check"

/-! ## `+` with a string operand

The one string operation this slice has, because the example above builds
its message with it. -/

#guard outcome [.exprStmt (.binary .add (.strLit "a") (.numLit 1.0))] == "a1"
#guard outcome [.exprStmt (.binary .add (.numLit 1.0) (.strLit "a"))] == "1a"
#guard outcome [.exprStmt (.binary .add (.strLit "x") .undefLit)] == "xundefined"
#guard outcome [.exprStmt (.binary .add (.numLit 1.0) (.numLit 2.0))] == "3"
