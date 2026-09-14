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
     {"type":"ExpressionStatement","expression":{
       "type":"BinaryExpression","operator":"**",
       "left":{"type":"Literal","value":2,"raw":"2"},
       "right":{"type":"Literal","value":3,"raw":"3"}}},
     {"type":"ForStatement",
      "init":{"type":"VariableDeclaration","kind":"let","declarations":[
        {"type":"VariableDeclarator","id":{"type":"Identifier","name":"i"},
         "init":{"type":"Literal","value":0,"raw":"0"}}]},
      "test":{"type":"BinaryExpression","operator":"<",
              "left":{"type":"Identifier","name":"i"},
              "right":{"type":"Literal","value":2,"raw":"2"}},
      "update":{"type":"UpdateExpression","operator":"++","prefix":false,
                "argument":{"type":"Identifier","name":"i"}},
      "body":{"type":"BlockStatement","body":[
        {"type":"ExpressionStatement","expression":{
          "type":"AssignmentExpression","operator":"+=",
          "left":{"type":"Identifier","name":"n"},
          "right":{"type":"Identifier","name":"i"}}},
        {"type":"SwitchStatement",
         "discriminant":{"type":"Identifier","name":"i"},
         "cases":[
           {"type":"SwitchCase","test":{"type":"Literal","value":0,"raw":"0"},
            "consequent":[{"type":"BreakStatement","label":null}]},
           {"type":"SwitchCase","test":null,"consequent":[{"type":"EmptyStatement"}]}]}]}},
     {"type":"VariableDeclaration","kind":"var","declarations":[
       {"type":"VariableDeclarator","id":{"type":"Identifier","name":"hoisted"},
        "init":{"type":"UnaryExpression","operator":"void","prefix":true,
                "argument":{"type":"Literal","value":0,"raw":"0"}}}]},
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
    -- `**` is an ESTree `BinaryExpression` like the rest; the parser has
    -- already resolved its right-associativity, so the decoder has
    -- nothing to say about it.
    .exprStmt (.binary .exponent (.numLit 2.0) (.numLit 3.0)),
    .forStmt (some (.decl .«let» [{ name := "i", init := some (.numLit 0.0) }]))
      (some (.binary .lt (.ident "i") (.numLit 2.0)))
      (some (.update .inc false (.ident "i")))
      (.block
        [ .exprStmt (.compoundAssign .add (.ident "n") (.ident "i")),
          .switchStmt (.ident "i")
            [ { test := some (.numLit 0.0), body := [.breakStmt none] },
              { test := none, body := [.empty] } ] ]),
    .varDecl .«var» [{ name := "hoisted", init := some (.unary .void (.numLit 0.0)) }],
    .exprStmt .undefLit ]

#guard decode wholeSliceJson == toString (repr wholeSlice)

/-! ## Classes

A class body's members in one document, beside the two shapes the class
nodes take: a declaration with a heritage clause whose constructor calls
`super` and whose method reads through it, and a named class
expression. -/

private def classSliceJson : String := script <|
  r#"{"type":"ClassDeclaration","id":{"type":"Identifier","name":"A"},"superClass":null,"body":{"type":"ClassBody","body":[{"type":"PropertyDefinition","key":{"type":"Identifier","name":"x"},"value":{"type":"Literal","value":1,"raw":"1"},"computed":false,"static":false},{"type":"PropertyDefinition","key":{"type":"Identifier","name":"y"},"value":null,"computed":false,"static":false},{"type":"PropertyDefinition","key":{"type":"PrivateIdentifier","name":"v"},"value":{"type":"Literal","value":2,"raw":"2"},"computed":false,"static":false},{"type":"PropertyDefinition","key":{"type":"Identifier","name":"s"},"value":{"type":"Literal","value":3,"raw":"3"},"computed":false,"static":true},{"type":"MethodDefinition","key":{"type":"Identifier","name":"constructor"},"value":{"type":"FunctionExpression","id":null,"params":[{"type":"Identifier","name":"v"}],"body":{"type":"BlockStatement","body":[{"type":"ExpressionStatement","expression":{"type":"AssignmentExpression","operator":"=","left":{"type":"MemberExpression","object":{"type":"ThisExpression"},"property":{"type":"PrivateIdentifier","name":"v"},"computed":false},"right":{"type":"Identifier","name":"v"}}}]},"async":false,"generator":false},"kind":"constructor","computed":false,"static":false},{"type":"MethodDefinition","key":{"type":"Identifier","name":"g"},"value":{"type":"FunctionExpression","id":null,"params":[],"body":{"type":"BlockStatement","body":[{"type":"ReturnStatement","argument":{"type":"MemberExpression","object":{"type":"ThisExpression"},"property":{"type":"PrivateIdentifier","name":"v"},"computed":false}}]},"async":false,"generator":false},"kind":"get","computed":false,"static":false},{"type":"MethodDefinition","key":{"type":"Identifier","name":"g"},"value":{"type":"FunctionExpression","id":null,"params":[{"type":"Identifier","name":"w"}],"body":{"type":"BlockStatement","body":[{"type":"ExpressionStatement","expression":{"type":"AssignmentExpression","operator":"=","left":{"type":"MemberExpression","object":{"type":"ThisExpression"},"property":{"type":"PrivateIdentifier","name":"v"},"computed":false},"right":{"type":"Identifier","name":"w"}}}]},"async":false,"generator":false},"kind":"set","computed":false,"static":false},{"type":"MethodDefinition","key":{"type":"Identifier","name":"m"},"value":{"type":"FunctionExpression","id":null,"params":[],"body":{"type":"BlockStatement","body":[{"type":"ReturnStatement","argument":{"type":"MemberExpression","object":{"type":"ThisExpression"},"property":{"type":"PrivateIdentifier","name":"v"},"computed":false}}]},"async":false,"generator":false},"kind":"method","computed":false,"static":false},{"type":"MethodDefinition","key":{"type":"Identifier","name":"sm"},"value":{"type":"FunctionExpression","id":null,"params":[],"body":{"type":"BlockStatement","body":[{"type":"ReturnStatement","argument":{"type":"Literal","value":4,"raw":"4"}}]},"async":false,"generator":false},"kind":"method","computed":false,"static":true}]}},{"type":"ClassDeclaration","id":{"type":"Identifier","name":"B"},"superClass":{"type":"Identifier","name":"A"},"body":{"type":"ClassBody","body":[{"type":"MethodDefinition","key":{"type":"Identifier","name":"constructor"},"value":{"type":"FunctionExpression","id":null,"params":[{"type":"Identifier","name":"v"}],"body":{"type":"BlockStatement","body":[{"type":"ExpressionStatement","expression":{"type":"CallExpression","callee":{"type":"Super"},"arguments":[{"type":"Identifier","name":"v"}]}}]},"async":false,"generator":false},"kind":"constructor","computed":false,"static":false},{"type":"MethodDefinition","key":{"type":"Identifier","name":"m"},"value":{"type":"FunctionExpression","id":null,"params":[],"body":{"type":"BlockStatement","body":[{"type":"ReturnStatement","argument":{"type":"CallExpression","callee":{"type":"MemberExpression","object":{"type":"Super"},"property":{"type":"Identifier","name":"m"},"computed":false},"arguments":[]}}]},"async":false,"generator":false},"kind":"method","computed":false,"static":false}]}},{"type":"VariableDeclaration","kind":"const","declarations":[{"type":"VariableDeclarator","id":{"type":"Identifier","name":"C"},"init":{"type":"ClassExpression","id":{"type":"Identifier","name":"N"},"superClass":null,"body":{"type":"ClassBody","body":[]}}}]}"#

/-- The program `classSliceJson` decodes to. -/
private def classSlice : Program :=
  [ .classDecl "A"
      { name := some "A", superClass := none,
        elements :=
          [ .field false (.«public» "x") (some (.numLit 1.0)),
            .field false (.«public» "y") none,
            .field false (.«private» "v") (some (.numLit 2.0)),
            .field true (.«public» "s") (some (.numLit 3.0)),
            .ctor ["v"] [.exprStmt (.assign (.privateMember .this "v") (.ident "v"))],
            .method .getter false "g" [] [.returnStmt (some (.privateMember .this "v"))],
            .method .setter false "g" ["w"]
              [.exprStmt (.assign (.privateMember .this "v") (.ident "w"))],
            .method .method false "m" [] [.returnStmt (some (.privateMember .this "v"))],
            .method .method true "sm" [] [.returnStmt (some (.numLit 4.0))] ] },
    .classDecl "B"
      { name := some "B", superClass := some (.ident "A"),
        elements :=
          [ .ctor ["v"] [.exprStmt (.superCall [.ident "v"])],
            .method .method false "m" []
              [.returnStmt (some (.call (.superMember "m") []))] ] },
    .varDecl .«const»
      [{ name := "C",
         init := some (.classExpr { name := some "N", superClass := none, elements := [] }) }] ]

#guard decode classSliceJson == toString (repr classSlice)


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
#guard decode (script r#"{"type":"Unsupported","kind":"ForInStatement"}"#)
  == "unsupported: ForInStatement"

-- A node type outside the schema altogether — what a producer other
-- than the bridge might send.
#guard decode (script r#"{"type":"WithStatement","object":null,"body":null}"#)
  == "unsupported: WithStatement"

-- An operator inside a known node but outside the slice.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"BinaryExpression","operator":"==",
        "left":{"type":"Literal","value":1,"raw":"1"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: BinaryExpression =="

-- The five arithmetic compound operators decode; every other spelling
-- names itself, because none of them has an operator the evaluator can
-- delegate to.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"AssignmentExpression","operator":"**=",
        "left":{"type":"Identifier","name":"n"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: AssignmentExpression **="

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"AssignmentExpression","operator":"&&=",
        "left":{"type":"Identifier","name":"n"},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: AssignmentExpression &&="

-- The two remaining unary operators ESTree spells here.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"UnaryExpression","operator":"~","prefix":true,
        "argument":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: UnaryExpression ~"

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"UnaryExpression","operator":"delete","prefix":true,
        "argument":{"type":"Identifier","name":"n"}}}"#)
  == "unsupported: UnaryExpression delete"

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

-- A `for` head with nothing in it is three `none`s.
#guard decode (script
    r#"{"type":"ForStatement","init":null,"test":null,"update":null,
        "body":{"type":"EmptyStatement"}}"#)
  == toString (repr ([.forStmt none none none .empty] : Program))

-- A head whose declaration binds a pattern arrived as the bridge's
-- placeholder, and the pattern names the refusal; the loop around it did
-- not have to be refused for it.
#guard decode (script
    r#"{"type":"ForStatement",
        "init":{"type":"Unsupported","kind":"ArrayBindingPattern"},
        "test":null,"update":null,"body":{"type":"EmptyStatement"}}"#)
  == "unsupported: ArrayBindingPattern"

-- A `var` head is the function's, and decodes like any other.
#guard decode (script
    r#"{"type":"ForStatement",
        "init":{"type":"VariableDeclaration","kind":"var","declarations":[
          {"type":"VariableDeclarator","id":{"type":"Identifier","name":"i"},
           "init":{"type":"Literal","value":0,"raw":"0"}}]},
        "test":null,"update":null,"body":{"type":"EmptyStatement"}}"#)
  == toString (repr
    ([.forStmt (some (.decl .«var» [{ name := "i", init := some (.numLit 0.0) }]))
        none none .empty] : Program))

-- An expression head is evaluated for its effect.
#guard decode (script
    r#"{"type":"ForStatement",
        "init":{"type":"Literal","value":1,"raw":"1"},
        "test":null,"update":null,"body":{"type":"EmptyStatement"}}"#)
  == toString (repr ([.forStmt (some (.expr (.numLit 1.0))) none none .empty] : Program))

-- The three loop forms that are not in the slice keep naming
-- themselves, and so does `in`.
#guard decode (script r#"{"type":"Unsupported","kind":"DoStatement"}"#)
  == "unsupported: DoStatement"

#guard decode (script r#"{"type":"Unsupported","kind":"ForOfStatement"}"#)
  == "unsupported: ForOfStatement"

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"BinaryExpression","operator":"in",
        "left":{"type":"Literal","value":"a","raw":"\"a\""},
        "right":{"type":"Identifier","name":"o"}}}"#)
  == "unsupported: BinaryExpression in"

-- `++` and `--` decode, both ways round; no other update operator
-- exists, but a producer other than the bridge could send one.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"UpdateExpression","operator":"--","prefix":true,
        "argument":{"type":"Identifier","name":"n"}}}"#)
  == toString (repr ([.exprStmt (.update .dec true (.ident "n"))] : Program))

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"UpdateExpression","operator":"??","prefix":true,
        "argument":{"type":"Identifier","name":"n"}}}"#)
  == "unsupported: UpdateExpression ??"

-- An update through a target the slice cannot write reports that target.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"UpdateExpression","operator":"++","prefix":false,
        "argument":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: AssignmentExpression target"

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

-- A private name is a name the class's scope resolves, not a property
-- key, so it decodes to a member form of its own.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"MemberExpression","computed":false,
        "object":{"type":"Identifier","name":"o"},
        "property":{"type":"PrivateIdentifier","name":"x"}}}"#)
  == toString (repr [Stmt.exprStmt (.privateMember (.ident "o") "x")])

-- `#x in o` leaves the slice twice over: `in` is not an operator here,
-- and the bridge already refused the bare `#x` in place, since a private
-- name is not an expression.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"BinaryExpression","operator":"in",
        "left":{"type":"Unsupported","kind":"PrivateIdentifier"},
        "right":{"type":"Identifier","name":"o"}}}"#)
  == "unsupported: BinaryExpression in"

-- `new.target` likewise; #393 owns the syntax.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"Unsupported","kind":"MetaProperty"}}"#)
  == "unsupported: MetaProperty"

/-! ## What a class may spell and this slice may not -/

/-- A class declaration around one member, for the refusals below. -/
private def classWith (member : String) : String :=
  script <|
    r#"{"type":"ClassDeclaration","id":{"type":"Identifier","name":"A"},
        "superClass":null,
        "body":{"type":"ClassBody","body":["# ++ member ++ r#"]}}"#

/-- A `FunctionExpression` value for a member, with the two flags set as
given. -/
private def methodValue (isAsync isGenerator : String) : String :=
  r#"{"type":"FunctionExpression","id":null,"params":[],
      "body":{"type":"BlockStatement","body":[]},
      "async":"# ++ isAsync ++ r#","generator":"# ++ isGenerator ++ "}"

-- A private method is a non-writable element rather than a property, so
-- it has semantics of its own and is refused by name.
#guard decode (classWith
    (r#"{"type":"MethodDefinition","kind":"method","computed":false,"static":false,
         "key":{"type":"PrivateIdentifier","name":"m"},
         "value":"# ++ methodValue "false" "false" ++ "}"))
  == "unsupported: MethodDefinition private"

#guard decode (classWith
    (r#"{"type":"MethodDefinition","kind":"method","computed":false,"static":false,
         "key":{"type":"Identifier","name":"m"},
         "value":"# ++ methodValue "true" "false" ++ "}"))
  == "unsupported: MethodDefinition async"

#guard decode (classWith
    (r#"{"type":"MethodDefinition","kind":"method","computed":false,"static":false,
         "key":{"type":"Identifier","name":"m"},
         "value":"# ++ methodValue "false" "true" ++ "}"))
  == "unsupported: MethodDefinition generator"

-- A numeric key would need ToPropertyKey at parse time, as an object
-- literal's would.
#guard decode (classWith
    (r#"{"type":"MethodDefinition","kind":"method","computed":false,"static":false,
         "key":{"type":"Literal","value":1,"raw":"1"},
         "value":"# ++ methodValue "false" "false" ++ "}"))
  == "unsupported: MethodDefinition numeric key"

#guard decode (classWith
    r#"{"type":"PropertyDefinition","computed":false,"static":false,
        "key":{"type":"Literal","value":1,"raw":"1"},"value":null}"#)
  == "unsupported: PropertyDefinition numeric key"

-- A static block is a scope with a `this` of its own; a computed key and
-- an `accessor` field each stand in the member's place.
#guard decode (classWith r#"{"type":"Unsupported","kind":"ClassStaticBlockDeclaration"}"#)
  == "unsupported: ClassStaticBlockDeclaration"

#guard decode (classWith r#"{"type":"Unsupported","kind":"ComputedPropertyName"}"#)
  == "unsupported: ComputedPropertyName"

#guard decode (classWith r#"{"type":"Unsupported","kind":"AccessorKeyword"}"#)
  == "unsupported: AccessorKeyword"

-- `super.x = v` writes to the receiver rather than through the home
-- object, which is a target form of its own.
#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"AssignmentExpression","operator":"=",
        "left":{"type":"MemberExpression","computed":false,
                "object":{"type":"Super"},
                "property":{"type":"Identifier","name":"x"}},
        "right":{"type":"Literal","value":1,"raw":"1"}}}"#)
  == "unsupported: AssignmentExpression super target"

-- A member whose `value` is not a function, a body that is not a
-- `ClassBody`, and a `Super` where no rule admits one are all producer
-- errors rather than refusals.
#guard decode (classWith
    r#"{"type":"MethodDefinition","kind":"method","computed":false,"static":false,
        "key":{"type":"Identifier","name":"m"},
        "value":{"type":"Identifier","name":"f"}}"#)
  == "malformed: MethodDefinition value is a Identifier"

#guard decode (script
    r#"{"type":"ClassDeclaration","id":{"type":"Identifier","name":"A"},
        "superClass":null,"body":{"type":"BlockStatement","body":[]}}"#)
  == "malformed: class body is a BlockStatement"

#guard decode (script
    r#"{"type":"ExpressionStatement","expression":{
        "type":"CallExpression","callee":{"type":"Identifier","name":"f"},
        "arguments":[{"type":"Super"}]}}"#)
  == "malformed: Super outside a call or member access"

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

-- A `switch` whose clause list holds something that is not a clause:
-- the bridge has no other node to put there, so the producer is broken
-- rather than the program being outside the slice.
#guard decode (script
    r#"{"type":"SwitchStatement","discriminant":{"type":"Literal","value":1,"raw":"1"},
        "cases":[{"type":"BlockStatement","body":[]}]}"#)
  == "malformed: switch case is a BlockStatement"

-- And a clause whose `consequent` is not a list of statements.
#guard decode (script
    r#"{"type":"SwitchStatement","discriminant":{"type":"Literal","value":1,"raw":"1"},
        "cases":[{"type":"SwitchCase","test":null,"consequent":null}]}"#)
  == "malformed: field \"consequent\" is not an array"

-- A `for` head declaring nothing does not parse anywhere, so a document
-- with one did not come from a program.
#guard decode (script
    r#"{"type":"ForStatement",
        "init":{"type":"VariableDeclaration","kind":"let","declarations":[]},
        "test":null,"update":null,"body":{"type":"EmptyStatement"}}"#)
  == "malformed: VariableDeclaration has no declarators"

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
