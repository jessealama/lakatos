import Tarski.Eval
import Tarski.Format

/-! The host-defined surface test262 requires: `print`, `$262`, `typeof`
of a name that is not bound, and what an uncaught throw is reported as.

`print` has no IO to do. It appends ToString of its argument to
`%PrintLog%`, an intrinsic array, and `Tarski/Main.lean` writes the log
out once the run is over; `printed` below is what the binary would put on
stdout. `console.log` is the second output binding, `lakatos exe`'s
rather than test262's, and it writes to the same log — which is why a
program mixing the two still has one stdout in program order. `$262` exists and is empty: every hook the epic puts out of scope
is refused by the decoder (`DecodeTest`), so what is left is an object
for `typeof` to see and an absent `IsHTMLDDA` to read as `undefined`.

The report cases are the ones the runner reads. test262 names the class
of an uncaught error, and the runner matches that name off the binary's
`Uncaught <name>: <message>` line; `Test262Error` is not an `Error`
subclass, so the line has to come from the thrown object's *own*
`toString` rather than from its prototype chain. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- What `print` wrote during the run: the binary's stdout above the
completion value. -/
private def printed (p : Program) : List String :=
  match runScript p with
  | none => []
  | some (_, h) => h.printedLines

/-- A one-expression statement list. -/
private def stmt (e : Expr) : List Stmt := [.exprStmt e]

/-- `print(<e>);` -/
private def printStmt (e : Expr) : Stmt := .exprStmt (.call (.ident "print") [e])

/-- `console.log(<args>);` -/
private def consoleLogStmt (args : List Expr) : Stmt :=
  .exprStmt (.call (.member (.ident "console") "log") args)

/-! ## `print`

Each call is ToString of its first argument, in order. A call's own
completion value is `undefined`, which is what `print` answers. -/

#guard printed [printStmt (.strLit "a"), printStmt (.binary .add (.numLit 1.0) (.numLit 1.0))]
  == ["a", "2"]

#guard outcome [printStmt (.strLit "a")] == "undefined"

/-! A missing argument is `undefined`, as everywhere else. -/
#guard printed [.exprStmt (.call (.ident "print") [])] == ["undefined"]

/-! ToString of an object runs its `toString`. -/
#guard printed
    [printStmt (.objectLit [.init "toString" (.funcExpr none [] [.returnStmt (some (.strLit "t"))])])]
  == ["t"]

/-! A plain object's `toString` is `Object.prototype`'s. -/
#guard printed [printStmt (.objectLit [])] == ["[object Object]"]

/-! Nothing binds `%PrintLog%`, so an empty run has an empty log. -/
#guard printed [.exprStmt (.numLit 1.0)] == []

/-! ## `console.log`

`lakatos exe`'s output binding (#386), and `print`'s twin: it writes to
the *same* log, so a program that mixes the two gets one sequence in
program order. Unlike `print` it takes **every** argument through
ToString and joins the parts with one space.

`console.log("a", 1);` -/
#guard printed [consoleLogStmt [.strLit "a", .numLit 1.0]] == ["a 1"]

/-! No argument at all is one empty line, as it is under Node.

`console.log();` -/
#guard printed [consoleLogStmt []] == [""]

/-! One log, in program order.

`console.log(1, 2); print("x");` -/
#guard printed [consoleLogStmt [.numLit 1.0, .numLit 2.0], printStmt (.strLit "x")]
  == ["1 2", "x"]

/-! ToString, not Node's inspection: `-0` prints as `0` where Node prints
`-0`. The README names this as a limit of `exe`.

`console.log(-0);` -/
#guard printed [consoleLogStmt [.unary .neg (.numLit 0.0)]] == ["0"]

/-! A user `toString` runs, as it does for `print`.

`console.log({ toString() { return "t"; } });` -/
#guard printed
    [consoleLogStmt [.objectLit [.method .method "toString" [] [.returnStmt (some (.strLit "t"))]]]]
  == ["t"]

/-! And a plain object prints the way `print({})` does, through
`Object.prototype.toString`.

`console.log({});` -/
#guard printed [consoleLogStmt [.objectLit []]] == ["[object Object]"]

/-! The call answers `undefined`, as `print` does.

`console.log("a");` -/
#guard outcome [consoleLogStmt [.strLit "a"]] == "undefined"

/-! `console` is an object and `console.log` a function. -/
#guard outcome (stmt (.unary .typeof (.ident "console"))) == "object"
#guard outcome (stmt (.unary .typeof (.member (.ident "console") "log"))) == "function"

/-! ## `typeof` of the host bindings -/

#guard outcome (stmt (.unary .typeof (.ident "print"))) == "function"
#guard outcome (stmt (.unary .typeof (.ident "$262"))) == "object"

/-! `$262` carries nothing, so `IsHTMLDDA` — which the suite reads to
decide whether the host has that exotic object — is `undefined`. -/
#guard outcome (stmt (.member (.ident "$262") "IsHTMLDDA")) == "undefined"

/-! ## `typeof` of an unresolvable name

`typeof` evaluates a reference, and an unresolvable one answers
`"undefined"` instead of throwing. That is the whole of the exception:
the name alone is still a `ReferenceError`. -/

#guard outcome (stmt (.unary .typeof (.ident "nope"))) == "undefined"
#guard outcome (stmt (.binary .strictEq (.unary .typeof (.ident "nope")) (.strLit "undefined")))
  == "true"
#guard outcome (stmt (.ident "nope")) == "uncaught: ReferenceError: nope is not defined"

/-! A name that *is* bound is read as usual — including one in the
temporal dead zone, which `typeof` does not excuse. -/
#guard outcome
    [ .varDecl .«let» [{ name := "x", init := some (.numLit 1.0) }],
      .exprStmt (.unary .typeof (.ident "x")) ]
  == "number"

/-! ## The uncaught report

`harness/sta.js`, as `HarnessTest` transcribes it: `Test262Error` is a
plain function with its own `prototype.toString`, and nothing on its
chain reaches `Error.prototype`. The runner reads the class name off this
line, so the line has to be the object's own `toString`. -/

private def sta : List Stmt :=
  [ .funcDecl "Test262Error" ["message"]
      [ .ifStmt (.unary .not (.binary .instanceof .this (.ident "Test262Error")))
          (.block [.returnStmt (some (.new (.ident "Test262Error") [.ident "message"]))])
          none,
        .exprStmt (.assign (.member .this "message")
          (.logical .or (.ident "message") (.strLit ""))) ],
    .exprStmt (.assign (.member (.ident "Test262Error") "thrower")
      (.funcExpr none ["message"]
        [.throwStmt (.new (.ident "Test262Error") [.ident "message"])])),
    .exprStmt (.assign (.member (.member (.ident "Test262Error") "prototype") "toString")
      (.funcExpr none []
        [.returnStmt (some (.binary .add (.strLit "Test262Error: ")
          (.member .this "message")))])) ]

#guard outcome (sta ++ [.throwStmt (.new (.ident "Test262Error") [.strLit "boom"])])
  == "uncaught: Test262Error: boom"

/-! An `Error` reports through `Error.prototype.toString`, as before. -/
#guard outcome [.throwStmt (.new (.ident "TypeError") [.strLit "t"])]
  == "uncaught: TypeError: t"

/-! An object with no `toString` of any kind falls back to the printed
form rather than replacing one uncaught throw with another. -/
#guard outcome [.throwStmt (.objectLit [])] == "uncaught: [object Object]"

/-! A primitive has no `toString` to run at all. -/
#guard outcome [.throwStmt (.numLit 1.0)] == "uncaught: 1"

/-! What `print` wrote before an uncaught throw is still the log: the
binary writes it out ahead of the report. -/
#guard printed (sta ++
    [ printStmt (.strLit "before"),
      .throwStmt (.new (.ident "Test262Error") [.strLit "boom"]) ])
  == ["before"]
