import Tarski.Eval
import Tarski.Format

/-! `delete` and `in`: `[[Delete]]` and `[[HasProperty]]`.

Both land with the descriptors rather than with the loops, because
neither can be written without them: `delete` refuses a
non-configurable key and `in` is the prototype walk `findProperty`
already performs for a write.

`delete` takes a *reference*, which is why it is an `Expr` of its own
rather than a `UnaryOp`: a bare identifier is the strict-mode early
error, reported here at the point of use as `super` and an out-of-scope
private name already are. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- A program that is one expression. -/
private def expr (e : Expr) : Program := [.exprStmt e]

/-- `const <n> = <e>;` -/
private def «let» (n : String) (e : Expr) : Stmt :=
  .varDecl .«const» [{ name := n, init := some e }]

/-- `<l> in <r>`. -/
private def inOp (l r : Expr) : Expr := .binary .«in» l r

/-! ## `delete`

A configurable own key goes; a key that is not there is `true` anyway;
a non-configurable one refuses. -/

#guard outcome
    [ «let» "o" (.objectLit [("x", .numLit 1.0)]),
      .exprStmt (.delete (.member (.ident "o") "x")) ]
  == "true"
#guard outcome
    [ «let» "o" (.objectLit [("x", .numLit 1.0)]),
      .exprStmt (.delete (.member (.ident "o") "x")),
      .exprStmt (inOp (.strLit "x") (.ident "o")) ]
  == "false"
#guard outcome (expr (.delete (.member (.objectLit []) "x"))) == "true"
#guard outcome
    [ «let» "o" (.objectLit []),
      .exprStmt (.call (.member (.ident "Object") "defineProperty")
        [.ident "o", .strLit "x", .objectLit [("value", .numLit 1.0)]]),
      .exprStmt (.delete (.member (.ident "o") "x")) ]
  == "uncaught: TypeError: Cannot delete property 'x' of #<Object>"

-- The computed spelling is the same operation on ToPropertyKey of the
-- key expression.
#guard outcome
    [ «let» "o" (.objectLit [("x", .numLit 1.0)]),
      .exprStmt (.delete (.index (.ident "o") (.strLit "x"))),
      .exprStmt (inOp (.strLit "x") (.ident "o")) ]
  == "false"

-- Deleting an array element leaves the length alone: the result is a
-- hole, which reads `undefined`.
#guard outcome
    [ «let» "xs" (.arrayLit [.numLit 1.0, .numLit 2.0]),
      .exprStmt (.delete (.index (.ident "xs") (.numLit 0.0))),
      .exprStmt (.member (.ident "xs") "length") ]
  == "2"
#guard outcome
    [ «let» "xs" (.arrayLit [.numLit 1.0, .numLit 2.0]),
      .exprStmt (.delete (.index (.ident "xs") (.numLit 0.0))),
      .exprStmt (.index (.ident "xs") (.numLit 0.0)) ]
  == "undefined"

-- An array's `length` and a string's `length` and indices are
-- non-configurable own properties.
#guard outcome (expr (.delete (.member (.arrayLit []) "length")))
  == "uncaught: TypeError: Cannot delete property 'length' of #<Object>"
#guard outcome (expr (.delete (.member (.strLit "s") "length")))
  == "uncaught: TypeError: Cannot delete property 'length' of #<Object>"
#guard outcome (expr (.delete (.index (.strLit "s") (.numLit 0.0))))
  == "uncaught: TypeError: Cannot delete property '0' of #<Object>"
#guard outcome (expr (.delete (.index (.strLit "s") (.numLit 5.0)))) == "true"

-- Any other base: a Number has no own properties to delete, a nullish
-- one is ToObject's refusal, and anything that is not a reference at all
-- is evaluated for its effects and answers `true`.
#guard outcome (expr (.delete (.member (.numLit 1.0) "x"))) == "true"
#guard outcome (expr (.delete (.member .nullLit "x")))
  == "uncaught: TypeError: Cannot read properties of null (reading 'x')"
#guard outcome (expr (.delete (.numLit 1.0))) == "true"
#guard outcome
    [ .varDecl .«let» [{ name := "n", init := some (.numLit 0.0) }],
      .exprStmt (.delete (.update .inc true (.ident "n"))),
      .exprStmt (.ident "n") ]
  == "1"

-- A bare identifier is the strict-mode early error, at the point of use.
#guard outcome (expr (.delete (.ident "x")))
  == "uncaught: SyntaxError: Delete of an unqualified identifier in strict mode."

/-! ## `in`

HasProperty, so the whole prototype chain answers; a non-object right
operand is a `TypeError` after ToPropertyKey has run on the left. -/

#guard outcome (expr (inOp (.strLit "a") (.objectLit [("a", .numLit 1.0)]))) == "true"
#guard outcome (expr (inOp (.strLit "b") (.objectLit [("a", .numLit 1.0)]))) == "false"
#guard outcome (expr (inOp (.strLit "toString") (.objectLit []))) == "true"
#guard outcome (expr (inOp (.strLit "toString") (.call (.member (.ident "Object") "create")
    [.nullLit])))
  == "false"
#guard outcome (expr (inOp (.numLit 1.0) (.arrayLit [.numLit 5.0, .numLit 6.0]))) == "true"
#guard outcome (expr (inOp (.numLit 2.0) (.arrayLit [.numLit 5.0, .numLit 6.0]))) == "false"
#guard outcome (expr (inOp (.strLit "length") (.arrayLit []))) == "true"
#guard outcome (expr (inOp (.strLit "name") (.funcExpr none [] []))) == "true"

-- A non-enumerable or accessor key is still *there*: `in` asks about
-- presence, not enumerability.
#guard outcome
    [ «let» "o" (.objectLit []),
      .exprStmt (.call (.member (.ident "Object") "defineProperty")
        [.ident "o", .strLit "x", .objectLit [("get", .funcExpr none [] [])]]),
      .exprStmt (inOp (.strLit "x") (.ident "o")) ]
  == "true"

#guard outcome (expr (inOp (.strLit "x") (.numLit 1.0)))
  == "uncaught: TypeError: Cannot use 'in' operator to search for 'x' in 1"
#guard outcome (expr (inOp (.strLit "length") (.strLit "s")))
  == "uncaught: TypeError: Cannot use 'in' operator to search for 'length' in s"

-- `in` does not coerce either operand, so `applyStrict` and
-- `applyCoercing` never see it; the key is ToPropertyKey's, which does
-- run a user `toString`.
#guard BinaryOp.coerces .«in» == false
#guard outcome
    [ «let» "k" (.objectLit
        [("toString", .funcExpr none [] [.returnStmt (some (.strLit "a"))])]),
      .exprStmt (inOp (.ident "k") (.objectLit [("a", .numLit 1.0)])) ]
  == "true"
