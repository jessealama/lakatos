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

private def boolField (j : Json) (name : String) : DecodeM Bool := do
  match (← field j name).getBool? with
  | .ok b => .ok b
  | .error _ => bad s!"field \"{name}\" is not a boolean"

private def arrayField (j : Json) (name : String) : DecodeM (List Json) := do
  match (← field j name).getArr? with
  | .ok a => .ok a.toList
  | .error _ => bad s!"field \"{name}\" is not an array"

/-- A named field that must be a `BlockStatement`, read as its statement
list. The message names the field, since a `try` has three of them. -/
private def blockField (j : Json) (name : String) : DecodeM (List Json) := do
  let block ← field j name
  match ← nodeType block with
  | "BlockStatement" => arrayField block "body"
  | other => bad s!"{name} is a {other}"

/-- A function form's body: a `BlockStatement`'s statement list. Its own
message, because "body" alone would not say which node was wrong. -/
private def bodyField (j : Json) : DecodeM (List Json) := do
  let body ← field j "body"
  match ← nodeType body with
  | "BlockStatement" => arrayField body "body"
  | other => bad s!"function body is a {other}"

/-- Refuse the two function flags whose semantics are outside this epic,
naming the form so the message says which node it was. -/
private def checkFunctionFlags (j : Json) (label : String) : DecodeM Unit := do
  if ← boolField j "async" then .error (.unsupported s!"{label} async")
  if ← boolField j "generator" then .error (.unsupported s!"{label} generator")

/-- A parameter list. Only a plain identifier is in the slice; anything
else arrived as the bridge's placeholder and names the kind it stood
for, so a default parameter is refused as `Parameter` and a destructured
one as its pattern. -/
private def decodeParams : List Json → DecodeM (List String)
  | [] => pure []
  | p :: rest => do
    match ← nodeType p with
    | "Identifier" => pure ((← strField p "name") :: (← decodeParams rest))
    | "Unsupported" => .error (.unsupported (← strField p "kind"))
    | other => bad s!"parameter is a {other}"

private def unaryOp (s : String) : DecodeM UnaryOp :=
  match s with
  | "-" => .ok .neg
  | "+" => .ok .plus
  | "!" => .ok .not
  | "typeof" => .ok .typeof
  | _ => .error (.unsupported s!"UnaryExpression {s}")

private def logicalOp (s : String) : DecodeM LogicalOp :=
  match s with
  | "&&" => .ok .and
  | "||" => .ok .or
  | _ => .error (.unsupported s!"LogicalExpression {s}")

private def binaryOp (s : String) : DecodeM BinaryOp :=
  match s with
  | "+" => .ok .add
  | "-" => .ok .sub
  | "*" => .ok .mul
  | "/" => .ok .div
  | "%" => .ok .rem
  | "**" => .ok .exponent
  | "<" => .ok .lt
  | "<=" => .ok .le
  | ">" => .ok .gt
  | ">=" => .ok .ge
  | "===" => .ok .strictEq
  | "!==" => .ok .strictNe
  | "instanceof" => .ok .instanceof
  | _ => .error (.unsupported s!"BinaryExpression {s}")

/-- A `Literal`, by the JSON type of its `value`. -/
private def decodeLiteral (j : Json) : DecodeM Expr := do
  match ← field j "value" with
  | .num n => pure (.numLit n.toFloat)
  | .bool b => pure (.boolLit b)
  | .null => pure .nullLit
  | .str s => pure (.strLit s)
  | _ => bad "Literal value is neither a number, a string, a boolean, nor null"

/-- An identifier's name; `undefined` is the literal, not a reference. -/
private def identExpr (name : String) : Expr :=
  if name == "undefined" then .undefLit else .ident name

/-- A `break` or `continue`'s target: an `Identifier`'s name, or nothing
for the unlabelled form. -/
private def jumpLabel (j : Json) : DecodeM (Option String) := do
  match ← optField j "label" with
  | none => pure none
  | some l =>
    match ← nodeType l with
    | "Identifier" => pure (some (← strField l "name"))
    | other => bad s!"jump label is a {other}"

/-- What an assignment can write to. Reading the target as an expression
first is what lets an out-of-slice one report itself: it arrived as the
bridge's placeholder and `decodeExpr` already named the kind it stood
for. -/
private def toTarget : Expr → DecodeM Target
  | .ident name => pure (.ident name)
  | .member object name => pure (.member object name)
  | .index object key => pure (.index object key)
  | _ => .error (.unsupported "AssignmentExpression target")

/-- The `$262` hooks the epic puts out of scope. Each is refused here, by
name, so a test that reaches for one is *unsupported* — the verdict the
runner should file — rather than a failure against an evaluator that
never claimed to have them. The `$262` object itself exists and is empty
(see `Tarski/Realm.lean`), so `typeof $262` and the absent `IsHTMLDDA`
read as the suite expects. -/
def hostHooks : List String :=
  ["evalScript", "createRealm", "detachArrayBuffer", "gc", "agent", "global",
   "AbstractModuleSource"]

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
  | "LogicalExpression" =>
    pure (.logical (← logicalOp (← strField j "operator"))
      (← decodeExpr (← field j "left")) (← decodeExpr (← field j "right")))
  | "ConditionalExpression" =>
    pure (.cond (← decodeExpr (← field j "test")) (← decodeExpr (← field j "consequent"))
      (← decodeExpr (← field j "alternate")))
  | "ThisExpression" => pure .this
  | "MemberExpression" => decodeMember j
  | "CallExpression" =>
    pure (.call (← decodeExpr (← field j "callee")) (← decodeExprs (← arrayField j "arguments")))
  | "NewExpression" =>
    pure (.new (← decodeExpr (← field j "callee")) (← decodeExprs (← arrayField j "arguments")))
  | "ArrayExpression" =>
    -- A hole and a spread arrived as `Unsupported` elements in place, so
    -- `decodeExpr` refuses the element and names the kind it stood for;
    -- nothing here is special-cased.
    pure (.arrayLit (← decodeExprs (← arrayField j "elements")))
  | "ObjectExpression" =>
    pure (.objectLit (← decodeProps (← arrayField j "properties")))
  | "FunctionExpression" =>
    checkFunctionFlags j "FunctionExpression"
    let name ← match ← optField j "id" with
      | some id => pure (some (← strField id "name"))
      | none => pure none
    pure (.funcExpr name (← decodeParams (← arrayField j "params"))
      (← decodeStmts (← bodyField j)))
  | "ArrowFunctionExpression" =>
    checkFunctionFlags j "ArrowFunctionExpression"
    let params ← decodeParams (← arrayField j "params")
    if ← boolField j "expression" then
      pure (.arrow params (.expr (← decodeExpr (← field j "body"))))
    else
      pure (.arrow params (.block (← decodeStmts (← bodyField j))))
  | "AssignmentExpression" =>
    let op ← strField j "operator"
    if op != "=" then .error (.unsupported s!"AssignmentExpression {op}")
    else
      -- Decoding the target as an expression first lets an out-of-slice
      -- one report itself: it arrived as the bridge's placeholder and
      -- names the kind it stood for, rather than being swallowed here.
      let target ← toTarget (← decodeExpr (← field j "left"))
      pure (.assign target (← decodeExpr (← field j "right")))
  | "Unsupported" => .error (.unsupported (← strField j "kind"))
  | other => .error (.unsupported other)

/-- A `MemberExpression`, whose `computed` flag says which spelling it
was. A dot access needs an identifier property; a property that is the
bridge's placeholder names the kind it stood for, which is how a private
name reports itself. A dotted `$262` hook is refused by name. The
computed spelling `$262["evalScript"]` and any alias of the object
escape that and read an absent property instead: a documented limit of
refusing syntactically, not a hole to plug here. -/
partial def decodeMember (j : Json) : DecodeM Expr := do
  let object ← decodeExpr (← field j "object")
  let property ← field j "property"
  if ← boolField j "computed" then
    pure (.index object (← decodeExpr property))
  else
    match ← nodeType property with
    | "Identifier" =>
      let name ← strField property "name"
      match object with
      | .ident "$262" =>
        if hostHooks.contains name then .error (.unsupported s!"$262.{name}")
        else pure (.member object name)
      | _ => pure (.member object name)
    | "Unsupported" => .error (.unsupported (← strField property "kind"))
    | other => bad s!"MemberExpression property is a {other}"

partial def decodeExprs : List Json → DecodeM (List Expr)
  | [] => pure []
  | e :: rest => do pure ((← decodeExpr e) :: (← decodeExprs rest))

/-- An object literal's members. A numeric key is admitted by the schema
and refused here: `{ 1: x }` would need ToPropertyKey at parse time, and
the slice's keys are written keys. -/
partial def decodeProps : List Json → DecodeM (List (String × Expr))
  | [] => pure []
  | p :: rest => do
    match ← nodeType p with
    | "Property" =>
      let key ← field p "key"
      let name ← match ← nodeType key with
        | "Identifier" => strField key "name"
        | "Literal" =>
          match ← field key "value" with
          | .str s => pure s
          | .num _ => .error (.unsupported "Property numeric key")
          | _ => bad "Property key literal is neither a string nor a number"
        | other => bad s!"Property key is a {other}"
      pure ((name, ← decodeExpr (← field p "value")) :: (← decodeProps rest))
    | "Unsupported" => .error (.unsupported (← strField p "kind"))
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
  | "FunctionDeclaration" =>
    checkFunctionFlags j "FunctionDeclaration"
    let name ← strField (← field j "id") "name"
    pure (.funcDecl name (← decodeParams (← arrayField j "params"))
      (← decodeStmts (← bodyField j)))
  | "ReturnStatement" =>
    match ← optField j "argument" with
    | some e => pure (.returnStmt (some (← decodeExpr e)))
    | none => pure (.returnStmt none)
  | "IfStatement" =>
    let test ← decodeExpr (← field j "test")
    let consequent ← decodeStmt (← field j "consequent")
    match ← optField j "alternate" with
    | some a => pure (.ifStmt test consequent (some (← decodeStmt a)))
    | none => pure (.ifStmt test consequent none)
  | "WhileStatement" =>
    pure (.whileStmt (← decodeExpr (← field j "test")) (← decodeStmt (← field j "body")))
  | "BlockStatement" => pure (.block (← decodeStmts (← arrayField j "body")))
  | "ThrowStatement" => pure (.throwStmt (← decodeExpr (← field j "argument")))
  | "TryStatement" =>
    let block ← decodeStmts (← blockField j "block")
    let handler ← match ← optField j "handler" with
      | some h => pure (some (← decodeCatch h))
      | none => pure none
    let finalizer ← match ← optField j "finalizer" with
      | some f => pure (some (← decodeStmts (← blockField j "finalizer")))
      | none => pure none
    -- `try { }` alone is a syntax error, so the bridge never sends one;
    -- a document that does is a broken producer, not a program outside
    -- the slice.
    if handler.isNone && finalizer.isNone then
      bad "TryStatement has neither handler nor finalizer"
    else pure (.tryStmt block handler finalizer)
  | "LabeledStatement" =>
    let label ← field j "label"
    match ← nodeType label with
    | "Identifier" =>
      pure (.labeled (← strField label "name") (← decodeStmt (← field j "body")))
    | other => bad s!"LabeledStatement label is a {other}"
  | "BreakStatement" => pure (.breakStmt (← jumpLabel j))
  | "ContinueStatement" => pure (.continueStmt (← jumpLabel j))
  | "Unsupported" => .error (.unsupported (← strField j "kind"))
  | other => .error (.unsupported other)

/-- A `CatchClause`. An out-of-slice parameter is refused in place — the
clause, and so the `try` around it, survives — which is the precedent a
function parameter set. -/
partial def decodeCatch (j : Json) : DecodeM CatchClause := do
  let param ← match ← optField j "param" with
    | none => pure none
    | some p =>
      match ← nodeType p with
      | "Identifier" => pure (some (← strField p "name"))
      | "Unsupported" => .error (.unsupported (← strField p "kind"))
      | other => bad s!"CatchClause param is a {other}"
  pure { param, body := ← decodeStmts (← blockField j "body") }

partial def decodeDeclarators : List Json → DecodeM (List Declarator)
  | [] => pure []
  | d :: rest => do pure ((← decodeDeclarator d) :: (← decodeDeclarators rest))

partial def decodeStmts : List Json → DecodeM (List Stmt)
  | [] => pure []
  | s :: rest => do pure ((← decodeStmt s) :: (← decodeStmts rest))

end

/-- Whether a statement node is a directive-prologue entry. A string
literal after the prologue carries no `directive` field and so decodes as
the ordinary expression statement it is. -/
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
