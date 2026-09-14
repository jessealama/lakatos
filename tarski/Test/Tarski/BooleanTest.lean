import Tarski.Eval
import Tarski.Format

/-! The `Boolean` intrinsic and the Boolean wrapper object.

`Boolean(v)` is ToBoolean and nothing else; `new Boolean(v)` boxes the
same answer. ToBoolean is total and calls no user code, so there is no
coercion order to observe here — what there is to observe is that **a
wrapper is an object and every object is truthy**, so
`new Boolean(false)` is a true condition while its `valueOf()` is
`false`. That pair is the whole reason the wrapper is worth building. -/

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

/-- `-0`. -/
private def negZero : Expr := .unary .neg (.numLit 0.0)

/-- `Boolean(<args>);` -/
private def boolCall (args : List Expr) : Expr := .call (.ident "Boolean") args

/-- `new Boolean(<args>)`. -/
private def newBool (args : List Expr) : Expr := .new (.ident "Boolean") args

/-- `Boolean.prototype`. -/
private def boolProto : Expr := .member (.ident "Boolean") "prototype"

/-! ## `Boolean` as a conversion — ToBoolean's seven falsy values -/

#guard outcome (expr (boolCall [])) == "false"
#guard outcome (expr (boolCall [.numLit 0.0])) == "false"
#guard outcome (expr (boolCall [negZero])) == "false"
#guard outcome (expr (boolCall [.strLit ""])) == "false"
#guard outcome (expr (boolCall [.ident "NaN"])) == "false"
#guard outcome (expr (boolCall [.nullLit])) == "false"
#guard outcome (expr (boolCall [.undefLit])) == "false"

#guard outcome (expr (boolCall [.numLit 1.0])) == "true"
#guard outcome (expr (boolCall [.strLit "a"])) == "true"
#guard outcome (expr (boolCall [.objectLit []])) == "true"
#guard outcome (expr (boolCall [.arrayLit []])) == "true"

-- `Boolean(new Boolean(false));` — an object is truthy, wrapper included.
#guard outcome (expr (boolCall [newBool [.boolLit false]])) == "true"

/-! ## The wrapper object: truthy, and `false` inside -/

#guard outcome (expr (.unary .typeof (newBool [.boolLit false]))) == "object"
#guard outcome (expr (.cond (newBool [.boolLit false]) (.numLit 1.0) (.numLit 2.0))) == "1"
#guard outcome (expr (.unary .not (newBool [.boolLit false]))) == "false"
#guard outcome (expr (.binary .strictEq (newBool [.boolLit false]) (.boolLit false))) == "false"

#guard outcome (expr (.call (.member (newBool [.boolLit false]) "valueOf") [])) == "false"
#guard outcome (expr (.call (.member (newBool [.numLit 1.0]) "valueOf") [])) == "true"
#guard outcome (expr (.call (.member (newBool []) "valueOf") [])) == "false"

/-! ## `Boolean.prototype.toString`

A primitive receiver and a wrapper receiver take the same path. -/

#guard outcome (expr (.call (.member (.boolLit true) "toString") [])) == "true"
#guard outcome (expr (.call (.member (.boolLit false) "toString") [])) == "false"
#guard outcome (expr (.call (.member (newBool [.boolLit true]) "toString") [])) == "true"

-- `new Boolean(false) + "";` — the number hint reaches `valueOf` first,
-- and `false + ""` is concatenation.
#guard outcome (expr (.binary .add (newBool [.boolLit false]) (.strLit ""))) == "false"

/-! ## `Boolean.prototype` is itself a Boolean object of value `false` -/

#guard outcome (expr (.call (.member boolProto "valueOf") [])) == "false"
#guard outcome (expr (.call (.member boolProto "toString") [])) == "false"

/-! ## Detached, the two methods refuse by name -/

#guard outcome
    [ .varDecl .«const» [{ name := "f", init := some (.member boolProto "valueOf") }],
      .exprStmt (.call (.ident "f") []) ]
  == "uncaught: TypeError: Boolean.prototype.valueOf requires that 'this' be a Boolean"
#guard outcome
    [ .varDecl .«const» [{ name := "g", init := some (.member boolProto "toString") }],
      .exprStmt (.call (.ident "g") []) ]
  == "uncaught: TypeError: Boolean.prototype.toString requires that 'this' be a Boolean"

/-! ## `Object(b)`, and a Boolean primitive as a property base -/

#guard outcome (expr (.call (.member (.call (.ident "Object") [.boolLit true]) "valueOf") []))
  == "true"
#guard outcome
    (expr (.binary .instanceof (.call (.ident "Object") [.boolLit false]) (.ident "Boolean")))
  == "true"
#guard outcome
    (expr (.binary .strictEq (.member (.boolLit true) "constructor") (.ident "Boolean")))
  == "true"
#guard outcome (expr (.call (.member (.boolLit true) "hasOwnProperty") [.strLit "x"])) == "false"

-- `[[BooleanData]]` is a field, not a key.
#guard outcome
    (expr (.member (.call (.member (.ident "Object") "keys") [newBool [.boolLit true]]) "length"))
  == "0"

#guard outcome (expr (.unary .typeof (.ident "Boolean"))) == "function"
