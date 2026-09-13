import Tarski.Decode

/-! The decoder against `schemas/tarski-estree.schema.json`.

The seam has two halves, and only one of them is checked in TypeScript:
`tarski/frontend/tests/estree.test.ts` proves the bridge emits documents
the schema accepts, and this file proves the Lean side reads exactly
those documents — and refuses everything else in the way the binary's
exit codes distinguish. An `unsupported` outcome says the evaluator does
not do this yet; a `malformed` one says the producer is broken. -/

open Lean Tarski

/-- Decode a document, answering either the program's `Repr` or the
message the binary would print. -/
private def decode (text : String) : String :=
  match Json.parse text with
  | .error msg => s!"not json: {msg}"
  | .ok j =>
    match decodeProgram j with
    | .error e => e.message
    | .ok p => toString (repr p)

private def prologue : String :=
  r#"{"type":"ExpressionStatement","expression":{"type":"Literal","value":"use strict","raw":"\"use strict\""},"directive":"use strict"}"#

private def script (body : String) : String :=
  "{\"type\":\"Program\",\"sourceType\":\"script\",\"body\":[" ++ prologue ++
    (if body.isEmpty then "" else "," ++ body) ++ "]}"

/-! ## Every node kind in the slice -/

private def wholeSliceJson : String := script <|
  r#"{"type":"VariableDeclaration","kind":"let","declarations":[
       {"type":"VariableDeclarator","id":{"type":"Identifier","name":"n"},
        "init":{"type":"Literal","value":0,"raw":"0"}},
       {"type":"VariableDeclarator","id":{"type":"Identifier","name":"seen"},
        "init":{"type":"Literal","value":false,"raw":"false"}}]},
     {"type":"VariableDeclaration","kind":"const","declarations":[
       {"type":"VariableDeclarator","id":{"type":"Identifier","name":"limit"},
        "init":{"type":"Literal","value":2.5,"raw":"2.5"}}]},
     {"type":"WhileStatement",
      "test":{"type":"BinaryExpression","operator":"<",
              "left":{"type":"Identifier","name":"n"},
              "right":{"type":"Identifier","name":"limit"}},
      "body":{"type":"BlockStatement","body":[
        {"type":"ExpressionStatement","expression":{
          "type":"AssignmentExpression","operator":"=",
          "left":{"type":"Identifier","name":"n"},
          "right":{"type":"BinaryExpression","operator":"+",
                   "left":{"type":"Identifier","name":"n"},
                   "right":{"type":"Literal","value":1,"raw":"1"}}}}]}},
     {"type":"IfStatement",
      "test":{"type":"UnaryExpression","operator":"!","prefix":true,
              "argument":{"type":"Identifier","name":"seen"}},
      "consequent":{"type":"ExpressionStatement","expression":{
        "type":"AssignmentExpression","operator":"=",
        "left":{"type":"Identifier","name":"seen"},
        "right":{"type":"Literal","value":true,"raw":"true"}}},
      "alternate":{"type":"ExpressionStatement","expression":{
        "type":"Literal","value":null,"raw":"null"}}},
     {"type":"ExpressionStatement","expression":{
       "type":"ConditionalExpression",
       "test":{"type":"BinaryExpression","operator":"===",
               "left":{"type":"Identifier","name":"n"},
               "right":{"type":"Literal","value":3,"raw":"3"}},
       "consequent":{"type":"Identifier","name":"n"},
       "alternate":{"type":"UnaryExpression","operator":"-","prefix":true,
                    "argument":{"type":"Literal","value":1,"raw":"1"}}}},
     {"type":"ExpressionStatement","expression":{"type":"Identifier","name":"undefined"}}"#

/-- The same program as an AST term. `undefined` is an ESTree
`Identifier` and decodes to the literal, not to a reference. -/
private def wholeSlice : Program :=
  [ .varDecl .«let»
      [ { name := "n", init := some (.numLit 0.0) },
        { name := "seen", init := some (.boolLit false) } ],
    .varDecl .«const» [{ name := "limit", init := some (.numLit 2.5) }],
    .whileStmt (.binary .lt (.ident "n") (.ident "limit"))
      (.block [.exprStmt (.assign "n" (.binary .add (.ident "n") (.numLit 1.0)))]),
    .ifStmt (.unary .not (.ident "seen"))
      (.exprStmt (.assign "seen" (.boolLit true)))
      (some (.exprStmt .nullLit)),
    .exprStmt (.cond (.binary .strictEq (.ident "n") (.numLit 3.0))
      (.ident "n") (.unary .neg (.numLit 1.0))),
    .exprStmt .undefLit ]

#guard decode wholeSliceJson == toString (repr wholeSlice)

-- A `let` declarator with no initializer binds `undefined`.
#guard decode (script
    r#"{"type":"VariableDeclaration","kind":"let","declarations":[
         {"type":"VariableDeclarator","id":{"type":"Identifier","name":"x"},"init":null}]}"#)
  == toString (repr ([.varDecl .«let» [{ name := "x", init := none }]] : Program))

-- An `if` with no `else`.
#guard decode (script
    r#"{"type":"IfStatement","test":{"type":"Literal","value":true,"raw":"true"},
        "consequent":{"type":"BlockStatement","body":[]},"alternate":null}"#)
  == toString (repr ([.ifStmt (.boolLit true) (.block []) none] : Program))

/-! ## Unsupported: the evaluator does not do this yet -/

-- The bridge's placeholder names the tsc kind it stood for, and that is
-- what the binary prints.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{"type":"Unsupported","kind":"TemplateExpression"}}"#)
  == "unsupported: TemplateExpression"

-- A placeholder in statement position, not just expression position.
#guard decode (script r#"{"type":"Unsupported","kind":"ForStatement"}"#)
  == "unsupported: ForStatement"

-- A node type outside the schema altogether — what a producer other
-- than the bridge might send.
#guard decode (script r#"{"type":"ForStatement","init":null,"test":null,"update":null}"#)
  == "unsupported: ForStatement"

-- An operator inside a known node but outside the slice.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"BinaryExpression","operator":"==",
        "left":{"type":"Literal","value":1,"raw":"1"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: BinaryExpression =="

-- Compound assignment is an `AssignmentExpression`, but not this
-- slice's.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"AssignmentExpression","operator":"+=",
        "left":{"type":"Identifier","name":"n"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: AssignmentExpression +="

-- `var` is a declaration kind the schema does not admit.
#guard decode (script
    r#"{"type":"VariableDeclaration","kind":"var","declarations":[
         {"type":"VariableDeclarator","id":{"type":"Identifier","name":"x"},"init":null}]}"#)
  == "unsupported: VariableDeclaration var"

/-! ## Malformed: whatever produced this is broken -/

-- A known node missing a required field.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"BinaryExpression","operator":"+",
        "left":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "malformed: missing field \"right\""

-- A field of the wrong JSON type.
#guard decode (script r#"{"type":"ExpressionStatement","expression":{"type":42}}"#)
  == "malformed: field \"type\" is not a string"

-- A declaration with no declarators.
#guard decode (script r#"{"type":"VariableDeclaration","kind":"let","declarations":[]}"#)
  == "malformed: VariableDeclaration has no declarators"

-- Strict mode is not optional: a script without the directive is
-- refused, and not as an unsupported node — every node in it may be in the
-- slice.
#guard decode "{\"type\":\"Program\",\"sourceType\":\"script\",\"body\":[]}"
  == "malformed: no \"use strict\" directive"

#guard decode
    ("{\"type\":\"Program\",\"sourceType\":\"script\",\"body\":[" ++
      r#"{"type":"ExpressionStatement","expression":{"type":"Literal","value":1,"raw":"1"}}"# ++ "]}")
  == "malformed: no \"use strict\" directive"

-- Modules are out of scope for the whole epic.
#guard decode "{\"type\":\"Program\",\"sourceType\":\"module\",\"body\":[]}"
  == "malformed: sourceType is not \"script\""

-- The root must be a `Program`.
#guard decode "{\"type\":\"Identifier\",\"name\":\"x\"}" == "unsupported: Identifier"
