import Lean.Data.Json
import Tarski.Ast

/-! Decoding `schemas/tarski-estree.schema.json` into the AST.

Strict in both directions: a node kind outside the slice is
`unsupported`, and a node kind inside it with the wrong shape is
`malformed`. The two are different outcomes because they mean different
things to a caller — the first says "tarski does not evaluate this
program yet", the second says "whatever produced this JSON is broken".

`Lean.Data.Json` is imported here and nowhere else in the evaluator, so
`Tarski.Eval`'s import footprint stays `Js` plus its own AST. -/

namespace Tarski

open Lean

/-- Why a document did not become a `Program`. -/
inductive DecodeError where
  /-- A node kind this slice does not evaluate. For the bridge's
  `Unsupported` placeholder this is the tsc SyntaxKind it stood for. -/
  | unsupported (kind : String)
  /-- A node this slice does evaluate, shaped wrongly. -/
  | malformed (msg : String)
deriving Repr, DecidableEq, Inhabited

/-- The decoder's message, as the binary prints it. -/
def DecodeError.message : DecodeError → String
  | .unsupported kind => s!"unsupported: {kind}"
  | .malformed msg => s!"malformed: {msg}"

/-- The decoder's monad. -/
abbrev DecodeM := Except DecodeError

private def bad {α : Type} (msg : String) : DecodeM α :=
  .error (.malformed msg)

/-- A node's field, or `malformed` naming it. -/
private def field (j : Json) (name : String) : DecodeM Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => bad s!"missing field \"{name}\""

private def strField (j : Json) (name : String) : DecodeM String := do
  match (← field j name).getStr? with
  | .ok s => .ok s
  | .error _ => bad s!"field \"{name}\" is not a string"

/-- A node's `type`, which every node in the schema has. -/
private def nodeType (j : Json) : DecodeM String := strField j "type"

/-- A field that is a node or JSON `null`. -/
private def optField (j : Json) (name : String) : DecodeM (Option Json) := do
  match ← field j name with
  | .null => pure none
  | v => pure (some v)

private def unaryOp (s : String) : DecodeM UnaryOp :=
  match s with
  | "-" => .ok .neg
  | "+" => .ok .plus
  | "!" => .ok .not
  | _ => .error (.unsupported s!"UnaryExpression {s}")

private def binaryOp (s : String) : DecodeM BinaryOp :=
  match s with
  | "+" => .ok .add
  | "-" => .ok .sub
  | "*" => .ok .mul
  | "/" => .ok .div
  | "%" => .ok .rem
  | "<" => .ok .lt
  | "<=" => .ok .le
  | ">" => .ok .gt
  | ">=" => .ok .ge
  | "===" => .ok .strictEq
  | "!==" => .ok .strictNe
  | _ => .error (.unsupported s!"BinaryExpression {s}")

/-- A `Literal`, by the JSON type of its `value`. A string literal is not
an expression in this slice: the only one the schema admits is a
directive's, and `decodeProgram` consumes that before it gets here. -/
private def decodeLiteral (j : Json) : DecodeM Expr := do
  match ← field j "value" with
  | .num n => pure (.numLit n.toFloat)
  | .bool b => pure (.boolLit b)
  | .null => pure .nullLit
  | .str _ => .error (.unsupported "Literal string")
  | _ => bad "Literal value is neither a number, a boolean, nor null"

/-- An identifier's name; `undefined` is the literal, not a reference. -/
private def identExpr (name : String) : Expr :=
  if name == "undefined" then .undefLit else .ident name

mutual

partial def decodeExpr (j : Json) : DecodeM Expr := do
  match ← nodeType j with
  | "Literal" => decodeLiteral j
  | "Identifier" => pure (identExpr (← strField j "name"))
  | "UnaryExpression" =>
    pure (.unary (← unaryOp (← strField j "operator")) (← decodeExpr (← field j "argument")))
  | "BinaryExpression" =>
    pure (.binary (← binaryOp (← strField j "operator"))
      (← decodeExpr (← field j "left")) (← decodeExpr (← field j "right")))
  | "ConditionalExpression" =>
    pure (.cond (← decodeExpr (← field j "test")) (← decodeExpr (← field j "consequent"))
      (← decodeExpr (← field j "alternate")))
  | "AssignmentExpression" =>
    let op ← strField j "operator"
    if op != "=" then .error (.unsupported s!"AssignmentExpression {op}")
    else
      let target ← field j "left"
      match ← nodeType target with
      | "Identifier" => pure (.assign (← strField target "name") (← decodeExpr (← field j "right")))
      | other => .error (.unsupported s!"AssignmentExpression target {other}")
  | "Unsupported" => .error (.unsupported (← strField j "kind"))
  | other => .error (.unsupported other)

partial def decodeDeclarator (j : Json) : DecodeM Declarator := do
  match ← nodeType j with
  | "VariableDeclarator" =>
    let id ← field j "id"
    let name ← strField id "name"
    match ← optField j "init" with
    | some e => pure { name, init := some (← decodeExpr e) }
    | none => pure { name, init := none }
  | other => .error (.unsupported other)

partial def decodeStmt (j : Json) : DecodeM Stmt := do
  match ← nodeType j with
  | "ExpressionStatement" => pure (.exprStmt (← decodeExpr (← field j "expression")))
  | "VariableDeclaration" =>
    let kind ← match ← strField j "kind" with
      | "let" => pure DeclKind.«let»
      | "const" => pure DeclKind.«const»
      | other => .error (.unsupported s!"VariableDeclaration {other}")
    match (← field j "declarations").getArr? with
    | .error _ => bad "VariableDeclaration declarations is not an array"
    | .ok ds =>
      if ds.isEmpty then bad "VariableDeclaration has no declarators"
      else pure (.varDecl kind (← decodeDeclarators ds.toList))
  | "IfStatement" =>
    let test ← decodeExpr (← field j "test")
    let consequent ← decodeStmt (← field j "consequent")
    match ← optField j "alternate" with
    | some a => pure (.ifStmt test consequent (some (← decodeStmt a)))
    | none => pure (.ifStmt test consequent none)
  | "WhileStatement" =>
    pure (.whileStmt (← decodeExpr (← field j "test")) (← decodeStmt (← field j "body")))
  | "BlockStatement" =>
    match (← field j "body").getArr? with
    | .error _ => bad "BlockStatement body is not an array"
    | .ok body => pure (.block (← decodeStmts body.toList))
  | "Unsupported" => .error (.unsupported (← strField j "kind"))
  | other => .error (.unsupported other)

partial def decodeDeclarators : List Json → DecodeM (List Declarator)
  | [] => pure []
  | d :: rest => do pure ((← decodeDeclarator d) :: (← decodeDeclarators rest))

partial def decodeStmts : List Json → DecodeM (List Stmt)
  | [] => pure []
  | s :: rest => do pure ((← decodeStmt s) :: (← decodeStmts rest))

end

/-- Whether a statement node is a directive-prologue entry. -/
private def isDirective (j : Json) : Bool :=
  match j.getObjVal? "directive" with
  | .ok _ => true
  | .error _ => false

/-- Decode a whole document. The script must be strict: its first
statement is required to be the `"use strict"` directive, which is
consumed. A sloppy script is not an unsupported *node* — every node in it
may be in the slice — so it is refused as malformed. -/
def decodeProgram (j : Json) : DecodeM Program := do
  match ← nodeType j with
  | "Program" => pure ()
  | other => .error (.unsupported other)
  if (← strField j "sourceType") != "script" then
    bad "sourceType is not \"script\""
  else
    match (← field j "body").getArr? with
    | .error _ => bad "Program body is not an array"
    | .ok body =>
      match body.toList with
      | [] => bad "no \"use strict\" directive"
      | first :: rest =>
        if !isDirective first then bad "no \"use strict\" directive"
        else if (← strField first "directive") != "use strict" then
          bad "first directive is not \"use strict\""
        else if rest.any isDirective then
          .error (.unsupported "Directive")
        else decodeStmts rest

end Tarski
