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
      (.block [.exprStmt (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))]),
    .ifStmt (.unary .not (.ident "seen"))
      (.exprStmt (.assign (.ident "seen") (.boolLit true)))
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

-- A target the slice cannot assign through reports itself: the bridge's
-- placeholder for the member access is what names the refusal.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"AssignmentExpression","operator":"=",
        "left":{"type":"Unsupported","kind":"PropertyAccessExpression"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: PropertyAccessExpression"

-- `undefined` is a literal, not a name, so it is not an assignable
-- target either.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"AssignmentExpression","operator":"=",
        "left":{"type":"Identifier","name":"undefined"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: AssignmentExpression target"

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

/-! ## Every node kind functions and objects added

A second whole-slice document, so the two halves of the seam stay
readable against one another as the slice grows. -/

private def objectSliceJson : String := script <|
  r#"{"type":"FunctionDeclaration","id":{"type":"Identifier","name":"add"},
      "params":[{"type":"Identifier","name":"a"},{"type":"Identifier","name":"b"}],
      "body":{"type":"BlockStatement","body":[
        {"type":"ReturnStatement","argument":{
          "type":"BinaryExpression","operator":"+",
          "left":{"type":"Identifier","name":"a"},
          "right":{"type":"Identifier","name":"b"}}}]},
      "async":false,"generator":false},
     {"type":"VariableDeclaration","kind":"const","declarations":[
       {"type":"VariableDeclarator","id":{"type":"Identifier","name":"o"},
        "init":{"type":"ObjectExpression","properties":[
          {"type":"Property","key":{"type":"Identifier","name":"a"},
           "value":{"type":"Literal","value":1,"raw":"1"},
           "kind":"init","computed":false,"shorthand":false,"method":false},
          {"type":"Property","key":{"type":"Literal","value":"b key","raw":"\"b key\""},
           "value":{"type":"Literal","value":"s","raw":"\"s\""},
           "kind":"init","computed":false,"shorthand":false,"method":false},
          {"type":"Property","key":{"type":"Identifier","name":"m"},
           "value":{"type":"FunctionExpression","id":null,"params":[],
                    "body":{"type":"BlockStatement","body":[
                      {"type":"ReturnStatement","argument":{"type":"ThisExpression"}}]},
                    "async":false,"generator":false},
           "kind":"init","computed":false,"shorthand":false,"method":false}]}}]},
     {"type":"VariableDeclaration","kind":"const","declarations":[
       {"type":"VariableDeclarator","id":{"type":"Identifier","name":"g"},
        "init":{"type":"ArrowFunctionExpression","id":null,
                "params":[{"type":"Identifier","name":"x"}],
                "body":{"type":"Identifier","name":"x"},
                "expression":true,"async":false,"generator":false}}]},
     {"type":"ExpressionStatement","expression":{
       "type":"AssignmentExpression","operator":"=",
       "left":{"type":"MemberExpression","computed":false,
               "object":{"type":"Identifier","name":"o"},
               "property":{"type":"Identifier","name":"a"}},
       "right":{"type":"Literal","value":2,"raw":"2"}}},
     {"type":"ExpressionStatement","expression":{
       "type":"CallExpression","arguments":[],
       "callee":{"type":"MemberExpression","computed":false,
                 "object":{"type":"Identifier","name":"o"},
                 "property":{"type":"Identifier","name":"m"}}}},
     {"type":"ExpressionStatement","expression":{
       "type":"NewExpression","callee":{"type":"Identifier","name":"add"},"arguments":[]}},
     {"type":"ExpressionStatement","expression":{
       "type":"LogicalExpression","operator":"&&",
       "left":{"type":"BinaryExpression","operator":"===",
               "left":{"type":"MemberExpression","computed":true,
                       "object":{"type":"Identifier","name":"o"},
                       "property":{"type":"Literal","value":"b key","raw":"\"b key\""}},
               "right":{"type":"Literal","value":"s","raw":"\"s\""}},
       "right":{"type":"BinaryExpression","operator":"===",
                "left":{"type":"UnaryExpression","operator":"typeof","prefix":true,
                        "argument":{"type":"MemberExpression","computed":false,
                                    "object":{"type":"Identifier","name":"o"},
                                    "property":{"type":"Identifier","name":"a"}}},
                "right":{"type":"Literal","value":"number","raw":"\"number\""}}}},
     {"type":"ExpressionStatement","expression":{
       "type":"CallExpression","callee":{"type":"Identifier","name":"g"},
       "arguments":[{"type":"Literal","value":3,"raw":"3"}]}},
     {"type":"ExpressionStatement","expression":{
       "type":"ArrayExpression","elements":[
         {"type":"Literal","value":1,"raw":"1"},
         {"type":"Literal","value":"a","raw":"\"a\""},
         {"type":"Identifier","name":"x"}]}}"#

/-- The same program as an AST term. A concise arrow body keeps its
`ArrowBody.expr` shape here; the evaluator is what reads it as a
`return`. -/
private def objectSlice : Program :=
  [ .funcDecl "add" ["a", "b"]
      [.returnStmt (some (.binary .add (.ident "a") (.ident "b")))],
    .varDecl .«const» [{ name := "o", init := some (.objectLit
      [ ("a", .numLit 1.0),
        ("b key", .strLit "s"),
        ("m", .funcExpr none [] [.returnStmt (some .this)]) ]) }],
    .varDecl .«const» [{ name := "g", init := some (.arrow ["x"] (.expr (.ident "x"))) }],
    .exprStmt (.assign (.member (.ident "o") "a") (.numLit 2.0)),
    .exprStmt (.call (.member (.ident "o") "m") []),
    .exprStmt (.new (.ident "add") []),
    .exprStmt (.logical .and
      (.binary .strictEq (.index (.ident "o") (.strLit "b key")) (.strLit "s"))
      (.binary .strictEq (.unary .typeof (.member (.ident "o") "a")) (.strLit "number"))),
    .exprStmt (.call (.ident "g") [.numLit 3.0]),
    .exprStmt (.arrayLit [.numLit 1.0, .strLit "a", .ident "x"]) ]

#guard decode objectSliceJson == toString (repr objectSlice)

-- A string statement after the prologue is an ordinary expression
-- statement: only a node carrying `directive` is one.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{"type":"Literal","value":"x","raw":"\"x\""}}"#)
  == toString (repr ([.exprStmt (.strLit "x")] : Program))

-- A `return` with no argument.
#guard decode (script
    r#"{"type":"FunctionDeclaration","id":{"type":"Identifier","name":"f"},"params":[],
        "body":{"type":"BlockStatement","body":[
          {"type":"ReturnStatement","argument":null}]},
        "async":false,"generator":false}"#)
  == toString (repr ([.funcDecl "f" [] [.returnStmt none]] : Program))

-- A block-bodied arrow.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"ArrowFunctionExpression","id":null,"params":[],
        "body":{"type":"BlockStatement","body":[]},
        "expression":false,"async":false,"generator":false}}"#)
  == toString (repr ([.exprStmt (.arrow [] (.block []))] : Program))

/-! ## Unsupported: functions and objects the slice refuses -/

-- `async` and `generator` are real syntax the epic does not model, so
-- the refusal names the flag and not the node kind.
#guard decode (script
    r#"{"type":"FunctionDeclaration","id":{"type":"Identifier","name":"f"},"params":[],
        "body":{"type":"BlockStatement","body":[]},"async":true,"generator":false}"#)
  == "unsupported: FunctionDeclaration async"

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"FunctionExpression","id":null,"params":[],
        "body":{"type":"BlockStatement","body":[]},"async":false,"generator":true}}"#)
  == "unsupported: FunctionExpression generator"

-- A default or rest parameter arrives as the `Parameter` it is, so the
-- function survives and only the parameter is refused.
#guard decode (script
    r#"{"type":"FunctionDeclaration","id":{"type":"Identifier","name":"f"},
        "params":[{"type":"Unsupported","kind":"Parameter"}],
        "body":{"type":"BlockStatement","body":[]},"async":false,"generator":false}"#)
  == "unsupported: Parameter"

-- A destructured parameter names its pattern.
#guard decode (script
    r#"{"type":"FunctionDeclaration","id":{"type":"Identifier","name":"f"},
        "params":[{"type":"Unsupported","kind":"ObjectBindingPattern"}],
        "body":{"type":"BlockStatement","body":[]},"async":false,"generator":false}"#)
  == "unsupported: ObjectBindingPattern"

-- A numeric key is admitted by the schema and refused here.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"ObjectExpression","properties":[
          {"type":"Property","key":{"type":"Literal","value":1,"raw":"1"},
           "value":{"type":"Literal","value":2,"raw":"2"},
           "kind":"init","computed":false,"shorthand":false,"method":false}]}}"#)
  == "unsupported: Property numeric key"

-- A shorthand, a method, an accessor, a computed key, and a spread all
-- arrive as placeholders in place.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"ObjectExpression","properties":[
          {"type":"Unsupported","kind":"ShorthandPropertyAssignment"}]}}"#)
  == "unsupported: ShorthandPropertyAssignment"

-- A private name is a property the slice does not read.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"MemberExpression","computed":false,
        "object":{"type":"Identifier","name":"o"},
        "property":{"type":"Unsupported","kind":"PrivateIdentifier"}}}"#)
  == "unsupported: PrivateIdentifier"

-- A spread argument is refused where it stands, not as the whole call.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"CallExpression","callee":{"type":"Identifier","name":"f"},
        "arguments":[{"type":"Unsupported","kind":"SpreadElement"}]}}"#)
  == "unsupported: SpreadElement"

/-! ## The `$262` host hooks

The epic puts `evalScript`, `createRealm`, `detachArrayBuffer`, `gc`,
`agent`, `global`, and `AbstractModuleSource` out of scope, and they are
refused here so that a test reaching for one is *unsupported* rather
than a failure. The refusal is syntactic: the dotted spelling on the
`$262` identifier itself, and nothing else. -/

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"CallExpression","callee":{
          "type":"MemberExpression","computed":false,
          "object":{"type":"Identifier","name":"$262"},
          "property":{"type":"Identifier","name":"evalScript"}},
        "arguments":[{"type":"Literal","value":1,"raw":"1"}]}}"#)
  == "unsupported: $262.evalScript"

-- The refusal is on the member access, so it reaches a caller through
-- any expression around it.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"CallExpression","callee":{
          "type":"MemberExpression","computed":false,
          "object":{"type":"MemberExpression","computed":false,
                    "object":{"type":"Identifier","name":"$262"},
                    "property":{"type":"Identifier","name":"agent"}},
          "property":{"type":"Identifier","name":"start"}},
        "arguments":[{"type":"Literal","value":"","raw":"\"\""}]}}"#)
  == "unsupported: $262.agent"

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"MemberExpression","computed":false,
        "object":{"type":"Identifier","name":"$262"},
        "property":{"type":"Identifier","name":"global"}}}"#)
  == "unsupported: $262.global"

-- A property that is not a hook is an ordinary access: `IsHTMLDDA` is
-- the one the suite reads to learn the host does not have it.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"MemberExpression","computed":false,
        "object":{"type":"Identifier","name":"$262"},
        "property":{"type":"Identifier","name":"IsHTMLDDA"}}}"#)
  == toString (repr ([.exprStmt (.member (.ident "$262") "IsHTMLDDA")] : Program))

-- The computed spelling escapes the refusal and reads an absent
-- property: a documented limit of refusing syntactically.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"MemberExpression","computed":true,
        "object":{"type":"Identifier","name":"$262"},
        "property":{"type":"Literal","value":"evalScript","raw":"\"evalScript\""}}}"#)
  == toString (repr ([.exprStmt (.index (.ident "$262") (.strLit "evalScript"))] : Program))

-- The same property name on any other object is untouched.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"MemberExpression","computed":false,
        "object":{"type":"Identifier","name":"o"},
        "property":{"type":"Identifier","name":"evalScript"}}}"#)
  == toString (repr ([.exprStmt (.member (.ident "o") "evalScript")] : Program))

-- A hole and a spread are refused where they stand, the array literal
-- around them surviving, as a call's spread argument is.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"ArrayExpression","elements":[
          {"type":"Literal","value":1,"raw":"1"},
          {"type":"Unsupported","kind":"OmittedExpression"},
          {"type":"Literal","value":2,"raw":"2"}]}}"#)
  == "unsupported: OmittedExpression"

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"ArrayExpression","elements":[
          {"type":"Unsupported","kind":"SpreadElement"},
          {"type":"Literal","value":1,"raw":"1"}]}}"#)
  == "unsupported: SpreadElement"

-- `??` is a logical operator the slice does not have.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"LogicalExpression","operator":"??",
        "left":{"type":"Identifier","name":"a"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: LogicalExpression ??"

/-! ## Malformed: the new nodes, shaped wrongly -/

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"CallExpression","callee":{"type":"Identifier","name":"f"}}}"#)
  == "malformed: missing field \"arguments\""

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"MemberExpression",
        "object":{"type":"Identifier","name":"o"},
        "property":{"type":"Identifier","name":"a"}}}"#)
  == "malformed: missing field \"computed\""

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{"type":"ArrayExpression"}}"#)
  == "malformed: missing field \"elements\""

-- A function body that is not a block: the bridge cannot produce one,
-- so this is the producer being broken rather than the slice's edge.
#guard decode (script
    r#"{"type":"FunctionDeclaration","id":{"type":"Identifier","name":"f"},"params":[],
        "body":{"type":"Identifier","name":"x"},"async":false,"generator":false}"#)
  == "malformed: function body is a Identifier"

/-! ## Every node kind exceptions and control flow added

A third whole-slice document, holding `throw`, the three shapes of `try`,
a labelled loop with both jumps in it, a bare `break`, and `instanceof`.
As with the two above, the document and the term are written out
separately so a change to either has to be a change to both. -/

private def controlSliceJson : String := script <|
  r#"{"type":"ThrowStatement","argument":{"type":"Literal","value":1,"raw":"1"}},
     {"type":"TryStatement",
      "block":{"type":"BlockStatement","body":[
        {"type":"ExpressionStatement","expression":{"type":"Identifier","name":"a"}}]},
      "handler":{"type":"CatchClause","param":{"type":"Identifier","name":"e"},
                 "body":{"type":"BlockStatement","body":[
                   {"type":"ExpressionStatement","expression":{"type":"Identifier","name":"e"}}]}},
      "finalizer":{"type":"BlockStatement","body":[
        {"type":"ExpressionStatement","expression":{"type":"Literal","value":2,"raw":"2"}}]}},
     {"type":"TryStatement",
      "block":{"type":"BlockStatement","body":[]},
      "handler":{"type":"CatchClause","param":null,
                 "body":{"type":"BlockStatement","body":[]}},
      "finalizer":null},
     {"type":"TryStatement",
      "block":{"type":"BlockStatement","body":[]},
      "handler":null,
      "finalizer":{"type":"BlockStatement","body":[]}},
     {"type":"LabeledStatement","label":{"type":"Identifier","name":"outer"},
      "body":{"type":"WhileStatement",
        "test":{"type":"Literal","value":true,"raw":"true"},
        "body":{"type":"BlockStatement","body":[
          {"type":"BreakStatement","label":{"type":"Identifier","name":"outer"}},
          {"type":"ContinueStatement","label":{"type":"Identifier","name":"outer"}}]}}},
     {"type":"BreakStatement","label":null},
     {"type":"ExpressionStatement","expression":{
       "type":"BinaryExpression","operator":"instanceof",
       "left":{"type":"Identifier","name":"x"},
       "right":{"type":"Identifier","name":"Y"}}}"#

private def controlSlice : Program :=
  [ .throwStmt (.numLit 1.0),
    .tryStmt [.exprStmt (.ident "a")]
      (some { param := some "e", body := [.exprStmt (.ident "e")] })
      (some [.exprStmt (.numLit 2.0)]),
    .tryStmt [] (some { param := none, body := [] }) none,
    .tryStmt [] none (some []),
    .labeled "outer"
      (.whileStmt (.boolLit true)
        (.block [.breakStmt (some "outer"), .continueStmt (some "outer")])),
    .breakStmt none,
    .exprStmt (.binary .instanceof (.ident "x") (.ident "Y")) ]

#guard decode controlSliceJson == toString (repr controlSlice)

/-! ## Unsupported: a catch parameter outside the slice -/

-- A destructuring `catch` binding is #394's. It is refused in place, so
-- the message names the pattern rather than the `try`.
#guard decode (script
    r#"{"type":"TryStatement","block":{"type":"BlockStatement","body":[]},
        "handler":{"type":"CatchClause",
                   "param":{"type":"Unsupported","kind":"ObjectBindingPattern"},
                   "body":{"type":"BlockStatement","body":[]}},
        "finalizer":null}"#)
  == "unsupported: ObjectBindingPattern"

/-! ## Malformed: exceptions and control flow, shaped wrongly -/

-- `try { }` alone does not parse, so the bridge never sends a
-- `TryStatement` with neither clause.
#guard decode (script
    r#"{"type":"TryStatement","block":{"type":"BlockStatement","body":[]},
        "handler":null,"finalizer":null}"#)
  == "malformed: TryStatement has neither handler nor finalizer"

#guard decode (script
    r#"{"type":"TryStatement","block":{"type":"Identifier","name":"x"},
        "handler":null,"finalizer":{"type":"BlockStatement","body":[]}}"#)
  == "malformed: block is a Identifier"

#guard decode (script
    r#"{"type":"LabeledStatement","label":{"type":"Literal","value":1,"raw":"1"},
        "body":{"type":"BlockStatement","body":[]}}"#)
  == "malformed: LabeledStatement label is a Literal"

#guard decode (script r#"{"type":"BreakStatement"}"#)
  == "malformed: missing field \"label\""
