import Test.ThalesEmit.Support

/-! The AST renderer: one guard per shape, because the rendering is total
and a shape it skipped would be a program the artifact claims to carry
and does not. Paths are relative to engines/thales, where every lake
invocation runs. -/

open Lean ThalesEmit

/-- A constructor `Tarski/Ast.lean` spells between guillemets cannot be
written inside a quotation: a `Name` component carries no escape, so the
quotation's `.«let»` and the renderer's are different trees. Those are
pinned as the text they print, which is what the guillemets are for. -/
def printsAs (x : RenderM Term) (expected : String) : CoreM Unit := do
  match RenderM.run x with
  | .error msg => throwError "render error: {msg}"
  | .ok t =>
    let text := (← PrettyPrinter.ppTerm ⟨unscope t.raw⟩).pretty 100
    unless text == expected do
      throwError "rendered {text}, expected {expected}"

/-! ## The issue's example -/

#guard rendersSyntax
  (programTerm [ .funcDecl "add" ["a", "b"]
    [ .returnStmt (some (.binary .add (.ident "a") (.ident "b"))) ] ])
  `([ .funcDecl "add" ["a", "b"]
    [ .returnStmt (some (.binary .add (.ident "a") (.ident "b"))) ] ])

/-! ## Literals

Numbers print through `Number::toString`, so what the artifact carries is
the one spelling the JS source, the bridge's JSON, the decoder, and a Lean
literal already share. -/

#guard rendersSyntax (exprTerm (.numLit 0.1)) `(.numLit 0.1)
#guard rendersSyntax (exprTerm (.numLit 5)) `(.numLit 5)
#guard rendersSyntax (exprTerm (.numLit 1e21)) `(.numLit 1e+21)
#guard rendersSyntax (exprTerm (.numLit 1e-7)) `(.numLit 1e-7)
#guard rendersSyntax (exprTerm (.numLit (1.0 / 3.0))) `(.numLit 0.3333333333333333)
#guard rendersSyntax (exprTerm (.numLit (-1.5))) `(.numLit (-1.5))
-- An overflow is `Infinity`, which has no literal: the library's constant
-- is the spelling, and the artifact's `open Js` makes it visible.
#guard rendersSyntax (exprTerm (.numLit (1e300 * 1e300))) `(.numLit floatInf)
#guard rendersSyntax (exprTerm (.numLit (-(1e300 * 1e300)))) `(.numLit (-floatInf))
#guard rendersSyntax (exprTerm (.strLit "a\"b\nc")) `(.strLit "a\"b\nc")
#guard rendersSyntax (exprTerm (.boolLit true)) `(.boolLit true)
#guard rendersSyntax (exprTerm (.boolLit false)) `(.boolLit false)
#guard rendersSyntax (exprTerm .undefLit) `(.undefLit)
#guard rendersSyntax (exprTerm .nullLit) `(.nullLit)

/-! ## Expressions -/

#guard rendersSyntax (exprTerm (.ident "x")) `(.ident "x")
#guard rendersSyntax (exprTerm .this) `(.this)
#guard rendersSyntax (exprTerm (.unary .neg (.ident "x"))) `(.unary .neg (.ident "x"))
#guard rendersSyntax (exprTerm (.unary .plus (.ident "x"))) `(.unary .plus (.ident "x"))
#guard rendersSyntax (exprTerm (.unary .not (.ident "x"))) `(.unary .not (.ident "x"))
#guard rendersSyntax (exprTerm (.unary .typeof (.ident "x"))) `(.unary .typeof (.ident "x"))
#guard rendersSyntax (exprTerm (.unary .void (.ident "x"))) `(.unary .void (.ident "x"))
#guard rendersSyntax (exprTerm (.binary .add (.ident "a") (.ident "b")))
  `(.binary .add (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .sub (.ident "a") (.ident "b")))
  `(.binary .sub (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .mul (.ident "a") (.ident "b")))
  `(.binary .mul (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .div (.ident "a") (.ident "b")))
  `(.binary .div (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .rem (.ident "a") (.ident "b")))
  `(.binary .rem (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .exponent (.ident "a") (.ident "b")))
  `(.binary .exponent (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .lt (.ident "a") (.ident "b")))
  `(.binary .lt (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .le (.ident "a") (.ident "b")))
  `(.binary .le (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .gt (.ident "a") (.ident "b")))
  `(.binary .gt (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .ge (.ident "a") (.ident "b")))
  `(.binary .ge (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .strictEq (.ident "a") (.ident "b")))
  `(.binary .strictEq (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .strictNe (.ident "a") (.ident "b")))
  `(.binary .strictNe (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.binary .instanceof (.ident "a") (.ident "b")))
  `(.binary .instanceof (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.logical .and (.ident "a") (.ident "b")))
  `(.logical .and (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.logical .or (.ident "a") (.ident "b")))
  `(.logical .or (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.cond (.ident "t") (.ident "a") (.ident "b")))
  `(.cond (.ident "t") (.ident "a") (.ident "b"))
#guard rendersSyntax (exprTerm (.member (.ident "o") "p")) `(.member (.ident "o") "p")
#guard rendersSyntax (exprTerm (.index (.ident "o") (.strLit "p")))
  `(.index (.ident "o") (.strLit "p"))
#guard rendersSyntax (exprTerm (.privateMember .this "v")) `(.privateMember .this "v")
#guard rendersSyntax (exprTerm (.superMember "p")) `(.superMember "p")
#guard rendersSyntax (exprTerm (.superIndex (.ident "k"))) `(.superIndex (.ident "k"))
#guard rendersSyntax (exprTerm (.superCall [.ident "x"])) `(.superCall [.ident "x"])
#guard rendersSyntax (exprTerm (.call (.ident "f") [])) `(.call (.ident "f") [])
#guard rendersSyntax (exprTerm (.call (.ident "f") [.ident "x", .numLit 1]))
  `(.call (.ident "f") [.ident "x", .numLit 1])
#guard rendersSyntax (exprTerm (.new (.ident "C") [.numLit 1]))
  `(.new (.ident "C") [.numLit 1])
#guard rendersSyntax (exprTerm (.arrayLit [])) `(.arrayLit [])
#guard rendersSyntax (exprTerm (.arrayLit [.numLit 1, .numLit 2]))
  `(.arrayLit [.numLit 1, .numLit 2])
#guard rendersSyntax (exprTerm (.objectLit [])) `(.objectLit [])
-- Every member form: a written key, a computed key, a method, an
-- accessor, and `__proto__:`. A key is spelled through its constructor
-- rather than the `Coe String PropKey` shorthand, so the two key shapes
-- read alike.
#guard rendersSyntax
  (exprTerm (.objectLit [.init (.name "a") (.numLit 1), .init (.computed (.ident "k")) (.ident "x")]))
  `(.objectLit [.init (.name "a") (.numLit 1), .init (.computed (.ident "k")) (.ident "x")])
#guard rendersSyntax (propDefTerm (.init (.name "b") (.ident "b")))
  `(.init (.name "b") (.ident "b"))
#guard rendersSyntax (propDefTerm (.method .method (.name "m") ["x"] [.returnStmt none]))
  `(.method .method (.name "m") ["x"] [.returnStmt none])
#guard rendersSyntax (propDefTerm (.method .getter (.computed (.strLit "g")) [] []))
  `(.method .getter (.computed (.strLit "g")) [] [])
#guard rendersSyntax (propDefTerm (.method .setter (.name "s") ["v"] []))
  `(.method .setter (.name "s") ["v"] [])
#guard rendersSyntax (propDefTerm (.proto (.ident "p"))) `(.proto (.ident "p"))
#guard rendersSyntax (propKeyTerm (.name "a")) `(.name "a")
#guard rendersSyntax (propKeyTerm (.computed (.numLit 1.5))) `(.computed (.numLit 1.5))
-- A template's strings are one more than its substitutions; a tagged
-- one carries its site number and both texts of each string, `cooked`
-- being `none` where the cooked grammar refuses the raw text.
#guard rendersSyntax (exprTerm (.template ["plain"] [])) `(.template ["plain"] [])
#guard rendersSyntax (exprTerm (.template ["a", "b", "c"] [.ident "x", .ident "y"]))
  `(.template ["a", "b", "c"] [.ident "x", .ident "y"])
#guard rendersSyntax
  (exprTerm (.taggedTemplate (.ident "tag") 0
    [{ cooked := some "x", raw := "x" }, { cooked := none, raw := "\\unicode" }] [.numLit 1]))
  `(.taggedTemplate (.ident "tag") 0
    [{ cooked := some "x", raw := "x" }, { cooked := none, raw := "\\unicode" }] [.numLit 1])
#guard rendersSyntax (exprTerm (.funcExpr none [] [.returnStmt none]))
  `(.funcExpr none [] [.returnStmt none])
#guard rendersSyntax (exprTerm (.funcExpr (some "f") ["x"] [.returnStmt (some (.ident "x"))]))
  `(.funcExpr (some "f") ["x"] [.returnStmt (some (.ident "x"))])
#guard rendersSyntax (exprTerm (.arrow ["x"] (.expr (.ident "x"))))
  `(.arrow ["x"] (.expr (.ident "x")))
#guard rendersSyntax (exprTerm (.arrow [] (.block [.returnStmt none])))
  `(.arrow [] (.block [.returnStmt none]))
#guard rendersSyntax (exprTerm (.assign (.ident "x") (.numLit 1)))
  `(.assign (.ident "x") (.numLit 1))
#guard rendersSyntax (exprTerm (.compoundAssign .add (.ident "x") (.numLit 1)))
  `(.compoundAssign .add (.ident "x") (.numLit 1))
#guard rendersSyntax (exprTerm (.update .inc true (.ident "x")))
  `(.update .inc true (.ident "x"))
#guard rendersSyntax (exprTerm (.update .dec false (.ident "x")))
  `(.update .dec false (.ident "x"))
#guard rendersSyntax (exprTerm (.delete (.member (.ident "o") "p")))
  `(.delete (.member (.ident "o") "p"))

/-! ## Targets -/

#guard rendersSyntax (targetTerm (.ident "x")) `(.ident "x")
#guard rendersSyntax (targetTerm (.member (.ident "o") "p")) `(.member (.ident "o") "p")
#guard rendersSyntax (targetTerm (.index (.ident "o") (.ident "k")))
  `(.index (.ident "o") (.ident "k"))
#guard rendersSyntax (targetTerm (.privateMember .this "v")) `(.privateMember .this "v")

/-! ## Parameters and declarators

A plain parameter is its name, through `Coe String Param`; a defaulted one
is the structure it is, so the two spellings sit side by side in one list. -/

#guard rendersSyntax (paramsTerm ["a", { name := "b", default := some (.numLit 1e21) }])
  `(["a", { name := "b", default := some (.numLit 1e+21) }])
#guard rendersSyntax (declaratorTerm { name := "x", init := none })
  `({ name := "x", init := none })
#guard rendersSyntax (declaratorTerm { name := "x", init := some (.numLit 1) })
  `({ name := "x", init := some (.numLit 1) })

/-! ## Statements -/

#guard rendersSyntax (stmtTerm (.exprStmt (.call (.ident "f") []))) `(.exprStmt (.call (.ident "f") []))
#guard rendersSyntax (stmtTerm (.funcDecl "f" [] [])) `(.funcDecl "f" [] [])
#guard rendersSyntax (stmtTerm (.returnStmt none)) `(.returnStmt none)
#guard rendersSyntax (stmtTerm (.returnStmt (some (.numLit 1)))) `(.returnStmt (some (.numLit 1)))
#guard rendersSyntax (stmtTerm (.ifStmt (.ident "t") .empty none))
  `(.ifStmt (.ident "t") .empty none)
#guard rendersSyntax (stmtTerm (.ifStmt (.ident "t") .empty (some (.block []))))
  `(.ifStmt (.ident "t") .empty (some (.block [])))
#guard rendersSyntax (stmtTerm (.whileStmt (.ident "t") .empty))
  `(.whileStmt (.ident "t") .empty)
#guard rendersSyntax (stmtTerm (.doWhileStmt .empty (.ident "t")))
  `(.doWhileStmt .empty (.ident "t"))
-- `for (;;)` is three `none`s.
#guard rendersSyntax (stmtTerm (.forStmt none none none .empty))
  `(.forStmt none none none .empty)
#guard rendersSyntax
  (stmtTerm (.forStmt (some (.expr (.ident "i"))) (some (.ident "t"))
    (some (.update .inc false (.ident "i"))) .empty))
  `(.forStmt (some (.expr (.ident "i"))) (some (.ident "t"))
    (some (.update .inc false (.ident "i"))) .empty)
#guard rendersSyntax
  (stmtTerm (.switchStmt (.ident "d")
    [{ test := some (.numLit 1), body := [.breakStmt none] },
     { test := none, body := [.returnStmt none] }]))
  `(.switchStmt (.ident "d")
    [{ test := some (.numLit 1), body := [.breakStmt none] },
     { test := none, body := [.returnStmt none] }])
#guard rendersSyntax (stmtTerm .empty) `(.empty)
#guard rendersSyntax (stmtTerm (.block [.empty])) `(.block [.empty])
#guard rendersSyntax (stmtTerm (.throwStmt (.ident "e"))) `(.throwStmt (.ident "e"))
-- A handler with no finalizer, and the reverse.
#guard rendersSyntax
  (stmtTerm (.tryStmt [] (some { param := some "e", body := [] }) none))
  `(.tryStmt [] (some { param := some "e", body := [] }) none)
#guard rendersSyntax (stmtTerm (.tryStmt [] none (some [.empty])))
  `(.tryStmt [] none (some [.empty]))
#guard rendersSyntax (stmtTerm (.tryStmt [] (some { param := none, body := [] }) none))
  `(.tryStmt [] (some { param := none, body := [] }) none)
#guard rendersSyntax (stmtTerm (.labeled "outer" .empty)) `(.labeled "outer" .empty)
#guard rendersSyntax (stmtTerm (.breakStmt none)) `(.breakStmt none)
#guard rendersSyntax (stmtTerm (.breakStmt (some "outer"))) `(.breakStmt (some "outer"))
#guard rendersSyntax (stmtTerm (.continueStmt none)) `(.continueStmt none)
#guard rendersSyntax (stmtTerm (.continueStmt (some "outer"))) `(.continueStmt (some "outer"))
#guard rendersSyntax (stmtTerm (.forInStmt (.target (.ident "k")) (.ident "o") .empty))
  `(.forInStmt (.target (.ident "k")) (.ident "o") .empty)

/-! ## Classes

Both sides of `isStatic` render; the design record's `Gate` — a private
field, a throwing constructor, a getter — goes through the decoder in the
round trip below. -/

#guard rendersSyntax (classDefTerm { name := none, superClass := none, elements := [] })
  `({ name := none, superClass := none, elements := [] })
#guard rendersSyntax
  (classDefTerm { name := some "B", superClass := some (.ident "A"), elements := [] })
  `({ name := some "B", superClass := some (.ident "A"), elements := [] })
#guard rendersSyntax (elementTerm (.ctor [] [])) `(.ctor [] [])
#guard rendersSyntax (elementTerm (.method .method false "m" ["x"] []))
  `(.method .method false "m" ["x"] [])
#guard rendersSyntax (elementTerm (.method .getter true "g" [] [])) `(.method .getter true "g" [] [])
#guard rendersSyntax (elementTerm (.method .setter false "s" ["v"] []))
  `(.method .setter false "s" ["v"] [])
-- `.field`'s key is a `ClassKey`, whose two constructors are keywords: it
-- is pinned as text below, with the rest of the guillemet spellings.
#guard rendersSyntax (exprTerm (.classExpr { name := none, superClass := none, elements := [] }))
  `(.classExpr { name := none, superClass := none, elements := [] })

/-! ## The guillemet spellings

`«let»`, `«const»`, `«var»`, `«in»`, `«public»`, and `«private»` are the
constructors whose names are Lean keywords. The printer does not escape a
`Name` component that is a keyword — `toString` escapes what is not
identifier-*shaped* — so the renderer puts the guillemets inside the
component, and that is pinned as text. -/

#eval show CoreM Unit from do
  printsAs (pure (declKindTerm .«let»)) ".«let»"
  printsAs (pure (declKindTerm .«const»)) ".«const»"
  printsAs (pure (declKindTerm .«var»)) ".«var»"
  printsAs (pure (binaryOpTerm .«in»)) ".«in»"
  printsAs (classKeyTerm (.«public» "n")) ".«public» \"n\""
  printsAs (classKeyTerm (.«private» "v")) ".«private» \"v\""
  printsAs (stmtTerm (.varDecl .«let» [{ name := "x", init := none }]))
    ".varDecl .«let» [{ name := \"x\", init := none }]"
  printsAs (stmtTerm (.varDecl .«const» [{ name := "x", init := some (.numLit 1) }]))
    ".varDecl .«const» [{ name := \"x\", init := some (.numLit 1) }]"
  printsAs (stmtTerm (.varDecl .«var» [{ name := "x", init := none }]))
    ".varDecl .«var» [{ name := \"x\", init := none }]"
  printsAs (forInitTerm (.decl .«let» [{ name := "i", init := some (.numLit 0) }]))
    ".decl .«let» [{ name := \"i\", init := some (.numLit 0) }]"
  printsAs (forInLeftTerm (.decl .«const» "k")) ".decl .«const» \"k\""
  printsAs (exprTerm (.binary .«in» (.strLit "p") (.ident "o")))
    ".binary .«in» (.strLit \"p\") (.ident \"o\")"
  printsAs (elementTerm (.field true (.«public» "n") (some (.numLit 0))))
    ".field true (.«public» \"n\") (some (.numLit 0))"
  printsAs (elementTerm (.field false (.«private» "v") none))
    ".field false (.«private» \"v\") none"

/-! ## The round trip, acceptance criterion 2

The rendered term is the decoder's output and nothing else: an ESTree
document goes through `Tarski.decodeProgram`, the result is rendered,
printed, parsed back, and elaborated, and the elaborated value is compared
to the decoded one. `repr` is the structural comparison — it is also what
distinguishes `-0` from `0`, which no decimal spelling does — and the
renderer's own text is the precision one, since `repr` prints six decimals
and could not tell `1e-7` from `2e-7`. -/

/-- The rendered term as text, losslessly: every number literal is
`Number::toString`'s answer, which round-trips to the double it came
from. -/
def renderText (p : Tarski.Program) : String :=
  match RenderM.run (programTerm p) with
  | .error msg => s!"render error: {msg}"
  | .ok t => toString (strip t.raw)

open Elab Command in
/-- Render, print, parse back, elaborate, compare. The def's name is built
with `mkIdent`: a name written literally inside the quotation would carry a
macro scope and not resolve. -/
def roundTrips (name : Name) (p : Tarski.Program) : CommandElabM Unit := do
  let text ← liftCoreM do
    match RenderM.run (astCommand (mkIdent name) p) with
    | .error msg => throwError msg
    | .ok cmd => pure (prettyLines (← PrettyPrinter.ppCommand ⟨unscope cmd.raw⟩))
  match Parser.runParserCategory (← getEnv) `command text with
  | .error e => throwError "the printed def does not parse: {e}\n{text}"
  | .ok stx =>
    elabCommand stx
    let id := mkIdent name
    elabCommand (← `(#guard toString (repr $id) == $(Syntax.mkStrLit (toString (repr p)))))
    elabCommand (← `(#guard renderText $id == $(Syntax.mkStrLit (renderText p))))

/-- A document's prologue, the directive `decodeProgram` consumes. -/
private def prologue : String :=
  "{\"type\":\"ExpressionStatement\"," ++
    "\"expression\":{\"type\":\"Literal\",\"value\":\"use strict\"," ++
    "\"raw\":\"\\\"use strict\\\"\"},\"directive\":\"use strict\"}"

private def script (body : String) : String :=
  "{\"type\":\"Program\",\"sourceType\":\"script\",\"body\":[" ++ prologue ++
    (if body.isEmpty then "" else "," ++ body) ++ "]}"

open Elab Command in
/-- Decode a document the way `thales-emit` does, then round-trip it. -/
def documentRoundTrips (name : Name) (body : String) : CommandElabM Unit := do
  let j ← match Json.parse (script body) with
    | .error msg => throwError "not json: {msg}"
    | .ok j => pure j
  match Tarski.decodeProgram j with
  | .error e => throwError "the document did not decode: {e.message}"
  | .ok p => roundTrips name p

/-- The bridge's own output for a script whose statements are the shapes
part (a) can only pin as text — the three declaration keywords, `in`, a
private field — beside the literals a six-decimal `repr` could not tell
apart. The source it came from:

```js
var x = 0.1;
let y = 1e+21, s = "a\"b\nc";
const z = 1e-7;
"p" in o;
class Gate {
    #lo;
    constructor(a) { throw new RangeError("lo"); }
    get lo() { return this.#lo; }
}
for (let i = 0; i < 3; i++) { }
for (const k in o) { }
```
-/
private def keywordsDoc : String := r#"{"type":"VariableDeclaration","kind":"var","declarations":[
     {"type":"VariableDeclarator","id":
     {"type":"Identifier","name":"x"},"init":
     {"type":"Literal","value":0.1,"raw":"0.1"}}]},
{"type":"VariableDeclaration","kind":"let","declarations":[
     {"type":"VariableDeclarator","id":
     {"type":"Identifier","name":"y"},"init":
     {"type":"Literal","value":1e+21,"raw":"1e+21"}},
     {"type":"VariableDeclarator","id":
     {"type":"Identifier","name":"s"},"init":
     {"type":"Literal","value":"a\"b\nc","raw":"\"a\\\"b\\nc\""}}]},
{"type":"VariableDeclaration","kind":"const","declarations":[
     {"type":"VariableDeclarator","id":
     {"type":"Identifier","name":"z"},"init":
     {"type":"Literal","value":1e-7,"raw":"1e-7"}}]},
{"type":"ExpressionStatement","expression":
     {"type":"BinaryExpression","operator":"in","left":
     {"type":"Literal","value":"p","raw":"\"p\""},"right":
     {"type":"Identifier","name":"o"}}},
{"type":"ClassDeclaration","id":
     {"type":"Identifier","name":"Gate"},"superClass":null,"body":
     {"type":"ClassBody","body":[
     {"type":"PropertyDefinition","key":
     {"type":"PrivateIdentifier","name":"lo"},"value":null,"computed":false,"static":false},
     {"type":"MethodDefinition","key":
     {"type":"Identifier","name":"constructor"},"value":
     {"type":"FunctionExpression","id":null,"params":[
     {"type":"Identifier","name":"a"}],"body":
     {"type":"BlockStatement","body":[
     {"type":"ThrowStatement","argument":
     {"type":"NewExpression","callee":
     {"type":"Identifier","name":"RangeError"},"arguments":[
     {"type":"Literal","value":"lo","raw":"\"lo\""}]}}]},"async":false,"generator":false},"kind":"constructor","computed":false,"static":false},
     {"type":"MethodDefinition","key":
     {"type":"Identifier","name":"lo"},"value":
     {"type":"FunctionExpression","id":null,"params":[],"body":
     {"type":"BlockStatement","body":[
     {"type":"ReturnStatement","argument":
     {"type":"MemberExpression","object":
     {"type":"ThisExpression"},"property":
     {"type":"PrivateIdentifier","name":"lo"},"computed":false}}]},"async":false,"generator":false},"kind":"get","computed":false,"static":false}]}},
{"type":"ForStatement","init":
     {"type":"VariableDeclaration","kind":"let","declarations":[
     {"type":"VariableDeclarator","id":
     {"type":"Identifier","name":"i"},"init":
     {"type":"Literal","value":0,"raw":"0"}}]},"test":
     {"type":"BinaryExpression","operator":"<","left":
     {"type":"Identifier","name":"i"},"right":
     {"type":"Literal","value":3,"raw":"3"}},"update":
     {"type":"UpdateExpression","operator":"++","argument":
     {"type":"Identifier","name":"i"},"prefix":false},"body":
     {"type":"BlockStatement","body":[]}},
{"type":"ForInStatement","left":
     {"type":"VariableDeclaration","kind":"const","declarations":[
     {"type":"VariableDeclarator","id":
     {"type":"Identifier","name":"k"},"init":null}]},"right":
     {"type":"Identifier","name":"o"},"body":
     {"type":"BlockStatement","body":[]}}"#

#eval show Elab.Command.CommandElabM Unit from
  documentRoundTrips `keywordsRoundTrip keywordsDoc

/-- The bridge's own output for the shapes #395 added: every object-literal
member form, an untagged template with and without substitutions, and two
tagged ones, the second holding a raw text the cooked grammar refuses. The
source it came from:

```js
const o = { a: 1, b, [k]: 2, 1.5: x, m() { return 1; }, get g() { return 2; }, set s(v) { }, __proto__: p };
`plain`;
`a${x}b${y}c`;
tag`x${1}y`;
tag`\unicode`;
```
-/
private def templatesDoc : String := r#"{"type":"VariableDeclaration","kind":"const","declarations":[{"type":"VariableDeclarator","id":{"type":"Identifier","name":"o"},"init":{"type":"ObjectExpression","properties":[{"type":"Property","key":{"type":"Identifier","name":"a"},"value":{"type":"Literal","value":1,"raw":"1"},"kind":"init","computed":false,"shorthand":false,"method":false},{"type":"Property","key":{"type":"Identifier","name":"b"},"value":{"type":"Identifier","name":"b"},"kind":"init","computed":false,"shorthand":true,"method":false},{"type":"Property","key":{"type":"Identifier","name":"k"},"value":{"type":"Literal","value":2,"raw":"2"},"kind":"init","computed":true,"shorthand":false,"method":false},{"type":"Property","key":{"type":"Literal","value":1.5,"raw":"1.5"},"value":{"type":"Identifier","name":"x"},"kind":"init","computed":false,"shorthand":false,"method":false},{"type":"Property","key":{"type":"Identifier","name":"m"},"value":{"type":"FunctionExpression","id":null,"params":[],"body":{"type":"BlockStatement","body":[{"type":"ReturnStatement","argument":{"type":"Literal","value":1,"raw":"1"}}]},"async":false,"generator":false},"kind":"init","computed":false,"shorthand":false,"method":true},{"type":"Property","key":{"type":"Identifier","name":"g"},"value":{"type":"FunctionExpression","id":null,"params":[],"body":{"type":"BlockStatement","body":[{"type":"ReturnStatement","argument":{"type":"Literal","value":2,"raw":"2"}}]},"async":false,"generator":false},"kind":"get","computed":false,"shorthand":false,"method":false},{"type":"Property","key":{"type":"Identifier","name":"s"},"value":{"type":"FunctionExpression","id":null,"params":[{"type":"Identifier","name":"v"}],"body":{"type":"BlockStatement","body":[]},"async":false,"generator":false},"kind":"set","computed":false,"shorthand":false,"method":false},{"type":"Property","key":{"type":"Identifier","name":"__proto__"},"value":{"type":"Identifier","name":"p"},"kind":"init","computed":false,"shorthand":false,"method":false}]}}]},{"type":"ExpressionStatement","expression":{"type":"TemplateLiteral","quasis":[{"type":"TemplateElement","value":{"cooked":"plain","raw":"plain"},"tail":true}],"expressions":[]}},{"type":"ExpressionStatement","expression":{"type":"TemplateLiteral","quasis":[{"type":"TemplateElement","value":{"cooked":"a","raw":"a"},"tail":false},{"type":"TemplateElement","value":{"cooked":"b","raw":"b"},"tail":false},{"type":"TemplateElement","value":{"cooked":"c","raw":"c"},"tail":true}],"expressions":[{"type":"Identifier","name":"x"},{"type":"Identifier","name":"y"}]}},{"type":"ExpressionStatement","expression":{"type":"TaggedTemplateExpression","tag":{"type":"Identifier","name":"tag"},"quasi":{"type":"TemplateLiteral","quasis":[{"type":"TemplateElement","value":{"cooked":"x","raw":"x"},"tail":false},{"type":"TemplateElement","value":{"cooked":"y","raw":"y"},"tail":true}],"expressions":[{"type":"Literal","value":1,"raw":"1"}]}}},{"type":"ExpressionStatement","expression":{"type":"TaggedTemplateExpression","tag":{"type":"Identifier","name":"tag"},"quasi":{"type":"TemplateLiteral","quasis":[{"type":"TemplateElement","value":{"cooked":null,"raw":"\\unicode"},"tail":true}],"expressions":[]}}}"#

#eval show Elab.Command.CommandElabM Unit from
  documentRoundTrips `templatesRoundTrip templatesDoc

open Elab Command in
/-- Every closure the store's emissions carry, round-tripped. These are the
bridge's own documents for the fixtures, so what is compared is the
decoder's reading of production input. -/
def emissionRoundTrips (tag emissionPath : String) : CommandElabM Unit := do
  let text ← IO.FS.readFile emissionPath
  let json ← IO.ofExcept (Json.parse text)
  let e ← IO.ofExcept (decodeEmission json)
  let mut n := 0
  for d in e.declarations do
    let ast := match d with
      | .fn f => f.ast | .cls c => c.ast | .const c => c.ast | .residual _ => none
    if let some (.program p) := ast then
      n := n + 1
      roundTrips (Name.mkSimple s!"roundTrip_{tag}_{n}") p
  if n == 0 then
    throwError "{emissionPath} carries no decoded closure to round-trip"

#eval show Elab.Command.CommandElabM Unit from
  emissionRoundTrips "tracer" "tests/fixtures/tracer.emission.json"
#eval show Elab.Command.CommandElabM Unit from
  emissionRoundTrips "statements" "tests/fixtures/statements.emission.json"
#eval show Elab.Command.CommandElabM Unit from
  emissionRoundTrips "classes" "tests/fixtures/classes.emission.json"
#eval show Elab.Command.CommandElabM Unit from
  emissionRoundTrips "module_consts" "tests/fixtures/module-consts.emission.json"
#eval show Elab.Command.CommandElabM Unit from
  emissionRoundTrips "operators" "tests/fixtures/operators.emission.json"
#eval show Elab.Command.CommandElabM Unit from
  emissionRoundTrips "degradations" "tests/fixtures/degradations.emission.json"
