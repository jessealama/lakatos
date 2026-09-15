import Lean.Data.Json
import Tarski.Ast

/-! Decoding `schemas/tarski-estree.schema.json` into the AST.

Strict in both directions: a node kind outside the slice is
`unsupported`, and a node kind inside it with the wrong shape is
`malformed`. The two are different outcomes because they mean different
things to a caller — the first says "tarski does not evaluate this
program yet", the second says "whatever produced this JSON is broken".

`Lean.Data.Json` is imported here and nowhere else in the evaluator, so
`Tarski.Eval`'s import footprint stays `Js` plus its own AST.

The monad carries one `Nat` of state, the next tagged-template site
number: a template object is cached per Parse Node, and this pass is the
one that sees the document in order. `decodeProgram` runs the state from
zero and answers an `Except`, so a caller never sees it.

Object literals arrive whole, spread included. A numeric key decodes as
a *computed* key over its `numLit`, so `{ 1.5: x }` takes its spelling
from ToPropertyKey at evaluation; an `async` or generator member is
`Property async` or `Property generator`.

Patterns arrive whole too, and `decodePattern` is one decoder for both
families: ESTree gives them one node family and the AST has one
`Pattern`. What the grammar refuses is `malformed` here — a
`RestElement` that is not last, a defaulted rest parameter, a compound
operator on a pattern, a pattern declarator with no initializer, and
`for await` — because the bridge emits none of them and a document that
does is a broken producer. An object rest whose argument is itself a
pattern is `unsupported`: it is real syntax (`({ ...[a] } = o)`) whose
early error this epic does not check.

Classes arrive whole. What a class may spell and the AST may not is
refused here by name: a private method or accessor (a non-writable
element, not a property), a numeric or computed key, an `async` or
generator member, a static block, an `accessor` field, a decorator, and
`super.x = v`. `new.target` and `#x in o` never reach this file — the
bridge has no node for either, so each arrives as a placeholder.

A string literal is decoded from its `raw` source text, not from its
`value`: `Lean.Json` replaces a lone surrogate with U+FFFD, so `"\uD800"`
would otherwise reach the evaluator as a string the source does not name.
The two are cross-checked wherever the literal is representable both
ways. A **legacy octal escape** is `unsupported` — a strict-mode early
error, refused by name rather than guessed at, and the second thing in
this file that says the word.

`Function(...)` and `new Function(...)` are refused here by name, as the
`$262` hooks are and for the same reason: the constructor's *semantics*
are `eval` by another spelling and outside the epic, while the intrinsic
itself must exist for `Function.prototype` to be reachable at all. An
alias — `const F = Function; F("x")` — escapes the refusal and meets a
`TypeError` instead, a documented limit of refusing syntactically. -/

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

/-- The decoder's monad. The state is the next tagged-template *site*
number: GetTemplateObject caches a template object per Parse Node, and
the decoder is the pass that walks the document in order, so it is what
numbers them. Nothing else reads or writes it. -/
abbrev DecodeM := StateT Nat (Except DecodeError)

private def bad {α : Type} (msg : String) : DecodeM α :=
  throw (.malformed msg)

/-- A node's field, or `malformed` naming it. -/
private def field (j : Json) (name : String) : DecodeM Json :=
  match j.getObjVal? name with
  | .ok v => pure v
  | .error _ => bad s!"missing field \"{name}\""

private def strField (j : Json) (name : String) : DecodeM String := do
  match (← field j name).getStr? with
  | .ok s => pure s
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
  | .ok b => pure b
  | .error _ => bad s!"field \"{name}\" is not a boolean"

private def arrayField (j : Json) (name : String) : DecodeM (List Json) := do
  match (← field j name).getArr? with
  | .ok a => pure a.toList
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
  if ← boolField j "async" then throw (.unsupported s!"{label} async")
  if ← boolField j "generator" then throw (.unsupported s!"{label} generator")

/-- A `VariableDeclaration`'s keyword. `var` joined the slice with the
`for` loop that needed it; every other spelling — there is none in ESTree
— names itself. -/
private def declKind (s : String) : DecodeM DeclKind :=
  match s with
  | "let" => pure .«let»
  | "const" => pure .«const»
  | "var" => pure .«var»
  | _ => throw (.unsupported s!"VariableDeclaration {s}")

private def unaryOp (s : String) : DecodeM UnaryOp :=
  match s with
  | "-" => pure .neg
  | "+" => pure .plus
  | "!" => pure .not
  | "typeof" => pure .typeof
  | "void" => pure .void
  | _ => throw (.unsupported s!"UnaryExpression {s}")

private def logicalOp (s : String) : DecodeM LogicalOp :=
  match s with
  | "&&" => pure .and
  | "||" => pure .or
  | _ => throw (.unsupported s!"LogicalExpression {s}")

private def binaryOp (s : String) : DecodeM BinaryOp :=
  match s with
  | "+" => pure .add
  | "-" => pure .sub
  | "*" => pure .mul
  | "/" => pure .div
  | "%" => pure .rem
  | "**" => pure .exponent
  | "<" => pure .lt
  | "<=" => pure .le
  | ">" => pure .gt
  | ">=" => pure .ge
  | "===" => pure .strictEq
  | "!==" => pure .strictNe
  | "instanceof" => pure .instanceof
  | "in" => pure .«in»
  | _ => throw (.unsupported s!"BinaryExpression {s}")

/-- The five compound assignment operators the evaluator takes, as the
`BinaryOp` each applies. Every other spelling ESTree admits is refused
under its own name: `**=` is not mapped onto `BinaryOp.exponent` yet,
the shifts and the bitwise forms need ToInt32, and `&&=`, `||=`, `??=`
short-circuit rather than apply an operator at all. -/
private def compoundOp (s : String) : DecodeM BinaryOp :=
  match s with
  | "+=" => pure .add
  | "-=" => pure .sub
  | "*=" => pure .mul
  | "/=" => pure .div
  | "%=" => pure .rem
  | _ => throw (.unsupported s!"AssignmentExpression {s}")

/-- An `UpdateExpression`'s operator. -/
private def updateOp (s : String) : DecodeM UpdateOp :=
  match s with
  | "++" => pure .inc
  | "--" => pure .dec
  | _ => throw (.unsupported s!"UpdateExpression {s}")

/-- One hexadecimal digit's value. -/
private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Exactly `n` hexadecimal digits, and what follows them. -/
private def takeHex : Nat → Nat → List Char → Option (Nat × List Char)
  | 0, acc, cs => some (acc, cs)
  | _ + 1, _, [] => none
  | n + 1, acc, c :: rest =>
    match hexDigit? c with
    | some d => takeHex n (acc * 16 + d) rest
    | none => none

/-- The digits of a `\u{…}` escape, up to the closing brace. At least one
digit is required, which is what makes `"\u{}"` malformed. -/
private def takeHexBrace (seen : Bool) (acc : Nat) : List Char → Option (Nat × List Char)
  | [] => none
  | '}' :: rest => if seen then some (acc, rest) else none
  | c :: rest =>
    match hexDigit? c with
    | some d => takeHexBrace true (acc * 16 + d) rest
    | none => none

/-- The StringLiteral escape grammar (12.9.4) over a literal's source
text, answering the code units it names.

A string literal is decoded from its **`raw`** rather than from its
`value` because `Lean.Json` cannot carry a lone surrogate: it reads
`"\ud800"` as U+FFFD, silently, so `"\uD800"` would reach the evaluator
as a different string than the one the source spells. The schema requires
`raw` on every `Literal`, so nothing on the bridge's side has to change.

A legacy octal escape is a strict-mode early error, and the epic does not
check early errors, so it is refused **by name** rather than guessed
at. -/
private partial def decodeLiteralChars : List Char → DecodeM (List UInt16)
  | [] => pure []
  | ['\\'] => bad "Literal raw ends in a backslash"
  | '\\' :: e :: rest => do
    let unit (u : Nat) : DecodeM (List UInt16) := do
      pure (UInt16.ofNat u :: (← decodeLiteralChars rest))
    match e with
    | 'b' => unit 0x8
    | 'f' => unit 0xC
    | 'n' => unit 0xA
    | 'r' => unit 0xD
    | 't' => unit 0x9
    | 'v' => unit 0xB
    | '0' =>
      match rest with
      | d :: _ => if '0' ≤ d && d ≤ '9' then throw (.unsupported "Literal octal escape") else unit 0
      | [] => unit 0
    | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' =>
      throw (.unsupported "Literal octal escape")
    | 'x' =>
      match takeHex 2 0 rest with
      | some (v, rest') => do pure (UInt16.ofNat v :: (← decodeLiteralChars rest'))
      | none => bad "Literal \\x escape is not two hex digits"
    | 'u' =>
      match rest with
      | '{' :: more =>
        match takeHexBrace false 0 more with
        | some (v, rest') =>
          if v ≤ 0x10FFFF then do
            pure (Js.JsString.encodeCodePoint v ++ (← decodeLiteralChars rest'))
          else bad "Literal \\u{…} escape is past the last code point"
        | none => bad "Literal \\u{…} escape is not hex digits in braces"
      | _ =>
        match takeHex 4 0 rest with
        | some (v, rest') => do pure (UInt16.ofNat v :: (← decodeLiteralChars rest'))
        | none => bad "Literal \\u escape is not four hex digits"
    -- A LineContinuation contributes nothing at all.
    | '\n' => decodeLiteralChars rest
    | '\r' =>
      match rest with
      | '\n' :: more => decodeLiteralChars more
      | _ => decodeLiteralChars rest
    | c =>
      if c.toNat == 0x2028 || c.toNat == 0x2029 then decodeLiteralChars rest
      -- NonEscapeCharacter: the backslash goes and the character stands.
      else do pure (Js.JsString.encodeCodePoint c.toNat ++ (← decodeLiteralChars rest))
  | c :: rest => do pure (Js.JsString.encodeCodePoint c.toNat ++ (← decodeLiteralChars rest))

/-- A string literal's source text — quotes and all — as code units. -/
private def decodeStringLiteral (raw : String) : DecodeM Js.JsString := do
  match raw.toList with
  | [] => bad "Literal raw is empty"
  | q :: rest =>
    if q != '"' && q != '\'' then bad "Literal raw is not a quoted string"
    else
      match rest.reverse with
      | [] => bad "Literal raw is not a quoted string"
      | q' :: body =>
        if q' != q then bad "Literal raw is not a quoted string"
        else do pure ⟨← decodeLiteralChars body.reverse⟩

/-- A `Literal`, by the JSON type of its `value`. -/
private def decodeLiteral (j : Json) : DecodeM Expr := do
  match ← field j "value" with
  | .num n => pure (.numLit n.toFloat)
  | .bool b => pure (.boolLit b)
  | .null => pure .nullLit
  | .str value => do
    let s ← decodeStringLiteral (← strField j "raw")
    -- Where the literal *is* representable as a Lean `String`, the escape
    -- grammar above is pinned against tsc's own reading of it, on every
    -- literal in every document the decoder ever sees.
    match Js.JsString.asString? s with
    | some str => if str == value then pure (.strLit s)
                  else bad "Literal raw disagrees with value"
    | none => pure (.strLit s)
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
  | .privateMember object name => pure (.privateMember object name)
  -- `super.x = v` is real syntax with semantics of its own — the write
  -- goes to the *receiver*, not through the home object — so it is
  -- refused by name rather than decoded as a member write.
  | .superMember _ | .superIndex _ => throw (.unsupported "AssignmentExpression super target")
  | _ => throw (.unsupported "AssignmentExpression target")

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
    -- `delete` is not a `UnaryOp`: it takes a reference rather than a
    -- value, so it is an `Expr` of its own. A `super` member operand is
    -- refused by name — `delete super.x` is a `ReferenceError` at
    -- runtime in the specification, which is semantics this AST does not
    -- carry.
    if (← strField j "operator") == "delete" then
      match ← decodeExpr (← field j "argument") with
      | .superMember _ | .superIndex _ => throw (.unsupported "UnaryExpression delete super")
      | operand => pure (.delete operand)
    else
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
  | "ClassExpression" => pure (.classExpr (← decodeClass j))
  | "CallExpression" =>
    let callee ← field j "callee"
    match ← nodeType callee with
    | "Super" => pure (.superCall (← decodeArgs (← arrayField j "arguments")))
    | _ =>
      match ← decodeExpr callee with
      | .ident "Function" => throw (.unsupported "Function constructor")
      | f => pure (.call f (← decodeArgs (← arrayField j "arguments")))
  -- `Super` is not an expression: it reaches here only as a call
  -- argument or some other position the schema does not allow it in.
  | "Super" => bad "Super outside a call or member access"
  | "NewExpression" =>
    match ← decodeExpr (← field j "callee") with
    | .ident "Function" => throw (.unsupported "Function constructor")
    | f => pure (.new f (← decodeArgs (← arrayField j "arguments")))
  | "TemplateLiteral" => decodeTemplate j
  -- The site number is taken after the tag is decoded and before the
  -- substitutions are, so a template nested in the tag numbers before
  -- this one and one nested in a substitution after it; every Parse
  -- Node gets a number of its own either way.
  | "TaggedTemplateExpression" =>
    let tag ← decodeExpr (← field j "tag")
    let quasi ← field j "quasi"
    match ← nodeType quasi with
    | "TemplateLiteral" => pure ()
    | other => bad s!"TaggedTemplateExpression quasi is a {other}"
    let site ← getModify (· + 1)
    let (strings, exprs) ← decodeTemplateParts quasi
    pure (.taggedTemplate tag site strings exprs)
  | "ArrayExpression" =>
    -- JSON `null` is an elision and a `SpreadElement` is a spread; both
    -- are ordinary elements of the list, as ESTree has them.
    pure (.arrayLit (← decodeArrayElements (← arrayField j "elements")))
  | "ObjectExpression" =>
    pure (.objectLit (← decodePropDefs (← arrayField j "properties")))
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
    -- Decoding the target as an expression first lets an out-of-slice one
    -- report itself: it arrived as the bridge's placeholder and names the
    -- kind it stood for, rather than being swallowed here.
    let op ← strField j "operator"
    let left ← field j "left"
    match ← nodeType left with
    | "ArrayPattern" | "ObjectPattern" =>
      -- Only `=` takes a pattern; `[a] += b` does not parse.
      if op == "=" then
        pure (.assignPattern (← decodePattern false left) (← decodeExpr (← field j "right")))
      else bad "AssignmentExpression pattern with a compound operator"
    | _ =>
      let target ← toTarget (← decodeExpr left)
      let value ← decodeExpr (← field j "right")
      if op == "=" then pure (.assign target value)
      else pure (.compoundAssign (← compoundOp op) target value)
  | "UpdateExpression" =>
    pure (.update (← updateOp (← strField j "operator")) (← boolField j "prefix")
      (← toTarget (← decodeExpr (← field j "argument"))))
  -- A spread outside a list that iterates it never reaches here: the
  -- decoder's three list readers take it, and the schema puts it nowhere
  -- else.
  | "SpreadElement" => bad "SpreadElement outside a list"
  | "Unsupported" => throw (.unsupported (← strField j "kind"))
  | other => throw (.unsupported other)

/-- An argument list, a `SpreadElement` in place. -/
partial def decodeArgs : List Json → DecodeM (List Expr)
  | [] => pure []
  | a :: rest => do
    match ← nodeType a with
    | "SpreadElement" =>
      pure (.spread (← decodeExpr (← field a "argument")) :: (← decodeArgs rest))
    | _ => pure ((← decodeExpr a) :: (← decodeArgs rest))

/-- An array literal's elements: JSON `null` is a hole, a `SpreadElement`
is a spread, and everything else is an ordinary expression. -/
partial def decodeArrayElements : List Json → DecodeM (List Expr)
  | [] => pure []
  | e :: rest => do
    if e.isNull then pure (.hole :: (← decodeArrayElements rest))
    else
      match ← nodeType e with
      | "SpreadElement" =>
        pure (.spread (← decodeExpr (← field e "argument")) ::
          (← decodeArrayElements rest))
      | _ => pure ((← decodeExpr e) :: (← decodeArrayElements rest))

/-- A `MemberExpression`, whose `computed` flag says which spelling it
was. A dot access needs an identifier property; a property that is the
bridge's placeholder names the kind it stood for, which is how a private
name reports itself. A dotted `$262` hook is refused by name. The
computed spelling `$262["evalScript"]` and any alias of the object
escape that and read an absent property instead: a documented limit of
refusing syntactically, not a hole to plug here. -/
partial def decodeMember (j : Json) : DecodeM Expr := do
  let objectNode ← field j "object"
  let isSuper := (← nodeType objectNode) == "Super"
  let property ← field j "property"
  if ← boolField j "computed" then
    let key ← decodeExpr property
    if isSuper then pure (.superIndex key)
    else pure (.index (← decodeExpr objectNode) key)
  else
    match ← nodeType property with
    | "Identifier" =>
      let name ← strField property "name"
      if isSuper then pure (.superMember name)
      else
        let object ← decodeExpr objectNode
        match object with
        | .ident "$262" =>
          if hostHooks.contains name then throw (.unsupported s!"$262.{name}")
          else pure (.member object name)
        | _ => pure (.member object name)
    | "PrivateIdentifier" =>
      pure (.privateMember (← decodeExpr objectNode) (← strField property "name"))
    | "Unsupported" => throw (.unsupported (← strField property "kind"))
    | other => bad s!"MemberExpression property is a {other}"

partial def decodeExprs : List Json → DecodeM (List Expr)
  | [] => pure []
  | e :: rest => do pure ((← decodeExpr e) :: (← decodeExprs rest))

/-- A field that is an expression or JSON `null`: a `for` head's three
parts and a `switch` clause's `test`, which is null for `default`. -/
partial def optExpr (j : Json) (name : String) : DecodeM (Option Expr) := do
  match ← optField j name with
  | none => pure none
  | some e => pure (some (← decodeExpr e))

/-- A parameter list. Every binding form is in the slice: an
`Identifier`, an `AssignmentPattern` over any pattern, an `ArrayPattern`
or `ObjectPattern`, and a `RestElement`. A `RestElement` that is not last
and a defaulted one do not parse, so either is `malformed`; anything
else arrived as the bridge's placeholder and names the kind it stood for,
which is how a TypeScript parameter property still reports itself. -/
partial def decodeParams : List Json → DecodeM (List Param)
  | [] => pure []
  | p :: rest => do
    match ← nodeType p with
    | "RestElement" =>
      if !rest.isEmpty then bad "RestElement is not last"
      else
        pure [{ target := ← decodePattern true (← field p "argument"), default := none,
                rest := true }]
    | "AssignmentPattern" =>
      let target ← decodePattern true (← field p "left")
      let d ← decodeExpr (← field p "right")
      pure ({ target, default := some d } :: (← decodeParams rest))
    | "Unsupported" => throw (.unsupported (← strField p "kind"))
    | _ =>
      pure ({ target := ← decodePattern true p, default := none } :: (← decodeParams rest))

/-- One binding or assignment pattern. The two families share a decoder
because they share an ESTree node family; what tells them apart is
`binding`, which is what makes a **binding** position — a parameter, a
declarator, a `catch` clause, a declaration loop head — admit only an
identifier leaf, as the grammar does. -/
partial def decodePattern (binding : Bool) (j : Json) : DecodeM Pattern := do
  match ← nodeType j with
  | "Identifier" => pure (.target (.ident (← strField j "name")))
  | "MemberExpression" =>
    if binding then bad "binding pattern leaf is a MemberExpression"
    else pure (.target (← toTarget (← decodeExpr j)))
  | "ArrayPattern" =>
    let (elements, rest) ← decodePatternElems binding (← arrayField j "elements")
    pure (.array elements rest)
  | "ObjectPattern" =>
    let (props, rest) ← decodePatternProps binding (← arrayField j "properties")
    pure (.object props rest)
  | "Unsupported" => throw (.unsupported (← strField j "kind"))
  | other => throw (.unsupported other)

/-- An `ArrayPattern`'s elements: JSON `null` is an elision, a
`RestElement` must be last, and anything else is an element with or
without a default. -/
partial def decodePatternElems (binding : Bool) :
    List Json → DecodeM (List (Option PatternElem) × Option Pattern)
  | [] => pure ([], none)
  | e :: rest => do
    if e.isNull then
      let (es, r) ← decodePatternElems binding rest
      pure (none :: es, r)
    else
      match ← nodeType e with
      | "RestElement" =>
        if !rest.isEmpty then bad "RestElement is not last"
        else pure ([], some (← decodePattern binding (← field e "argument")))
      | "AssignmentPattern" =>
        let target ← decodePattern binding (← field e "left")
        let d ← decodeExpr (← field e "right")
        let (es, r) ← decodePatternElems binding rest
        pure (some { target, default := some d } :: es, r)
      | _ =>
        let target ← decodePattern binding e
        let (es, r) ← decodePatternElems binding rest
        pure (some { target, default := none } :: es, r)

/-- An `ObjectPattern`'s properties. A `RestElement` must be last and its
argument must be a leaf, which is what the grammar says for both pattern
families. -/
partial def decodePatternProps (binding : Bool) :
    List Json → DecodeM (List PatternProp × Option Target)
  | [] => pure ([], none)
  | p :: rest => do
    match ← nodeType p with
    | "RestElement" =>
      if !rest.isEmpty then bad "RestElement is not last"
      else
        match ← decodePattern binding (← field p "argument") with
        | .target t => pure ([], some t)
        | _ => throw (.unsupported "RestElement pattern")
    | "Property" =>
      match ← strField p "kind" with
      | "init" =>
        if ← boolField p "method" then throw (.unsupported "Property method")
        else
          let key ← decodePropKey p
          let value ← field p "value"
          let prop ←
            match ← nodeType value with
            | "AssignmentPattern" =>
              pure { key, target := ← decodePattern binding (← field value "left"),
                     default := some (← decodeExpr (← field value "right")) }
            | _ =>
              pure { key, target := ← decodePattern binding value, default := none }
          let (ps, r) ← decodePatternProps binding rest
          pure (prop :: ps, r)
      | other => throw (.unsupported s!"Property {other}")
    | "Unsupported" => throw (.unsupported (← strField p "kind"))
    | other => throw (.unsupported other)

/-- An object literal member's key. A computed key is the expression in
the brackets; so is a *numeric* `Literal` key, which is what lets
`{ 1.5: x }` take its spelling from ToPropertyKey at evaluation rather
than from a second copy of `Number::toString` here. -/
partial def decodePropKey (p : Json) : DecodeM PropKey := do
  let key ← field p "key"
  if ← boolField p "computed" then
    pure (.computed (← decodeExpr key))
  else
    match ← nodeType key with
    | "Identifier" => pure (.name (← strField key "name"))
    | "Literal" =>
      match ← field key "value" with
      | .str s => pure (.name s)
      | .num n => pure (.computed (.numLit n.toFloat))
      | _ => bad "Property key literal is neither a string nor a number"
    | "Unsupported" => throw (.unsupported (← strField key "kind"))
    | other => bad s!"Property key is a {other}"

/-- A member whose value must be a `FunctionExpression`: a method, a
getter, or a setter. `async` and generator members are refused as
`Property async` and `Property generator`, the names `checkFunctionFlags`
gives every other function form. -/
partial def decodePropMethod (p : Json) (kind : MethodKind) (label : String) :
    DecodeM PropDef := do
  let key ← decodePropKey p
  let value ← field p "value"
  match ← nodeType value with
  | "FunctionExpression" => pure ()
  | other => bad s!"Property {label} value is a {other}"
  checkFunctionFlags value "Property"
  pure (.method kind key (← decodeParams (← arrayField value "params"))
    (← decodeStmts (← bodyField value)))

/-- An object literal's members, spread included. A shorthand needs no
arm of its own: ESTree gives it a `value` that is its own `Identifier`,
so `{ undefined }` binds `.undefLit` exactly as `undefined` alone does. -/
partial def decodePropDefs : List Json → DecodeM (List PropDef)
  | [] => pure []
  | p :: rest => do
    match ← nodeType p with
    | "Property" =>
      let member ← match ← strField p "kind" with
        | "get" => decodePropMethod p .getter "get"
        | "set" => decodePropMethod p .setter "set"
        | "init" =>
          if ← boolField p "method" then decodePropMethod p .method "method"
          else do
            let key ← decodePropKey p
            let value ← field p "value"
            -- B.3.1: only a written, non-shorthand `__proto__` sets the
            -- prototype. `{ ["__proto__"]: v }` and `{ __proto__ }` are
            -- ordinary members, which is what the specification's
            -- `IsComputedPropertyKey` test and the shorthand's own
            -- production say.
            match key with
            | .name "__proto__" =>
              if ← boolField p "shorthand" then pure (.init key (← decodeExpr value))
              else pure (.proto (← decodeExpr value))
            | _ => pure (.init key (← decodeExpr value))
        | other => throw (.unsupported s!"Property {other}")
      pure (member :: (← decodePropDefs rest))
    | "SpreadElement" =>
      pure (.spread (← decodeExpr (← field p "argument")) :: (← decodePropDefs rest))
    | "Unsupported" => throw (.unsupported (← strField p "kind"))
    | other => throw (.unsupported other)

/-- A `TemplateLiteral`'s quasis, in order. `value.cooked` is a string or
JSON `null`; `tail` says nothing the list order does not, so it is not
read. -/
partial def decodeTemplateStrings : List Json → DecodeM (List TemplateString)
  | [] => pure []
  | q :: rest => do
    match ← nodeType q with
    | "TemplateElement" =>
      let value ← field q "value"
      let cooked ← match ← field value "cooked" with
        | .null => pure none
        | .str s => pure (some s)
        | _ => bad "TemplateElement cooked is neither a string nor null"
      pure ({ cooked, raw := ← strField value "raw" } :: (← decodeTemplateStrings rest))
    | other => bad s!"TemplateLiteral quasi is a {other}"

/-- A `TemplateLiteral`'s two lists, checked against each other: there is
always one more quasi than there are substitutions. -/
partial def decodeTemplateParts (j : Json) :
    DecodeM (List TemplateString × List Expr) := do
  let strings ← decodeTemplateStrings (← arrayField j "quasis")
  let exprs ← decodeExprs (← arrayField j "expressions")
  if strings.length != exprs.length + 1 then
    bad s!"TemplateLiteral has {strings.length} quasis for {exprs.length} expressions"
  else pure (strings, exprs)

/-- A `TemplateLiteral` outside a tag. Its cooked strings are always
present: an invalid escape in an untagged template is a parse error, and
the bridge refuses a document that does not parse. -/
partial def decodeTemplate (j : Json) : DecodeM Expr := do
  let (strings, exprs) ← decodeTemplateParts j
  let cooked ← cookedStrings strings
  pure (.template cooked exprs)

/-- The cooked values of a template's quasis, refusing an absent one:
only a tagged template may carry one. -/
partial def cookedStrings : List TemplateString → DecodeM (List String)
  | [] => pure []
  | s :: rest =>
    match s.cooked with
    | none => bad "TemplateElement cooked is null outside a tag"
    | some c => do pure (c :: (← cookedStrings rest))

/-- A class element's key, and which side of the class it names. A
private method or accessor and a numeric key are refused: the first has
semantics of its own — a non-writable element rather than a property —
and the second would need ToPropertyKey at parse time, as an object
literal's numeric key would. A computed key arrived as the bridge's
placeholder and names itself. -/
partial def memberKey (j : Json) (label : String) : DecodeM String := do
  let key ← field j "key"
  match ← nodeType key with
  | "Identifier" => strField key "name"
  | "PrivateIdentifier" => throw (.unsupported s!"{label} private")
  | "Literal" =>
    match ← field key "value" with
    | .str s => pure s
    | .num _ => throw (.unsupported s!"{label} numeric key")
    | _ => bad s!"{label} key literal is neither a string nor a number"
  | "Unsupported" => throw (.unsupported (← strField key "kind"))
  | other => bad s!"{label} key is a {other}"

/-- A `PropertyDefinition`'s key, which may be private. -/
partial def fieldKey (j : Json) : DecodeM ClassKey := do
  let key ← field j "key"
  match ← nodeType key with
  | "PrivateIdentifier" => pure (.«private» (← strField key "name"))
  | _ => pure (.«public» (← memberKey j "PropertyDefinition"))

/-- A `ClassBody`'s members, in source order. Anything the bridge could
not put here arrived as its placeholder — a static block, a computed
key, an `accessor` field, a decorator, a TS-only modifier — and names
the kind it stood for. -/
partial def decodeElements : List Json → DecodeM (List ClassElement)
  | [] => pure []
  | m :: rest => do
    match ← nodeType m with
    | "MethodDefinition" =>
      let value ← field m "value"
      match ← nodeType value with
      | "FunctionExpression" => pure ()
      | other => bad s!"MethodDefinition value is a {other}"
      checkFunctionFlags value "MethodDefinition"
      let params ← decodeParams (← arrayField value "params")
      let body ← decodeStmts (← bodyField value)
      let isStatic ← boolField m "static"
      let element ← match ← strField m "kind" with
        -- A `static constructor` is an ordinary static method of that
        -- name; the bridge emits it as one, so only the instance side
        -- reaches this arm.
        | "constructor" => pure (ClassElement.ctor params body)
        | "method" =>
          pure (.method .method isStatic (← memberKey m "MethodDefinition") params body)
        | "get" =>
          pure (.method .getter isStatic (← memberKey m "MethodDefinition") params body)
        | "set" =>
          pure (.method .setter isStatic (← memberKey m "MethodDefinition") params body)
        | other => throw (.unsupported s!"MethodDefinition {other}")
      pure (element :: (← decodeElements rest))
    | "PropertyDefinition" =>
      let key ← fieldKey m
      let value ← optExpr m "value"
      pure (.field (← boolField m "static") key value :: (← decodeElements rest))
    | "Unsupported" => throw (.unsupported (← strField m "kind"))
    | other => throw (.unsupported other)

/-- A `ClassDeclaration` or `ClassExpression`'s shared shape. -/
partial def decodeClass (j : Json) : DecodeM ClassDef := do
  let name ← match ← optField j "id" with
    | some id => pure (some (← strField id "name"))
    | none => pure none
  let superClass ← optExpr j "superClass"
  let body ← field j "body"
  match ← nodeType body with
  | "ClassBody" => pure ()
  | other => bad s!"class body is a {other}"
  pure { name, superClass, elements := ← decodeElements (← arrayField body "body") }

partial def decodeDeclarator (j : Json) : DecodeM Declarator := do
  match ← nodeType j with
  | "VariableDeclarator" =>
    let target ← decodePattern true (← field j "id")
    match ← optField j "init" with
    | some e => pure { target, init := some (← decodeExpr e) }
    | none =>
      -- A binding pattern with no initializer does not parse.
      match target with
      | .target _ => pure { target, init := none }
      | _ => bad "VariableDeclarator pattern without initializer"
  | other => throw (.unsupported other)

partial def decodeStmt (j : Json) : DecodeM Stmt := do
  match ← nodeType j with
  | "ExpressionStatement" => pure (.exprStmt (← decodeExpr (← field j "expression")))
  | "VariableDeclaration" =>
    pure (.varDecl (← declKind (← strField j "kind")) (← declaratorList j))
  | "FunctionDeclaration" =>
    checkFunctionFlags j "FunctionDeclaration"
    let name ← strField (← field j "id") "name"
    pure (.funcDecl name (← decodeParams (← arrayField j "params"))
      (← decodeStmts (← bodyField j)))
  | "ClassDeclaration" =>
    pure (.classDecl (← strField (← field j "id") "name") (← decodeClass j))
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
  | "DoWhileStatement" =>
    -- The body comes first here as it does in the source: it runs before
    -- the first test, which is the whole of the difference from `while`.
    pure (.doWhileStmt (← decodeStmt (← field j "body")) (← decodeExpr (← field j "test")))
  | "ForStatement" =>
    let init ← match ← optField j "init" with
      | none => pure none
      | some head =>
        match ← nodeType head with
        | "VariableDeclaration" => pure (some (.decl (← declKind (← strField head "kind"))
            (← declaratorList head)))
        | _ => pure (some (.expr (← decodeExpr head)))
    let test ← optExpr j "test"
    let update ← optExpr j "update"
    pure (.forStmt init test update (← decodeStmt (← field j "body")))
  | "ForInStatement" =>
    pure (.forInStmt (← decodeLoopHead j) (← decodeExpr (← field j "right"))
      (← decodeStmt (← field j "body")))
  | "ForOfStatement" =>
    -- `for await` is an async iteration and stays outside the epic; the
    -- bridge refuses the `await` modifier in place, so a document with
    -- `"await": true` is a broken producer.
    if ← boolField j "await" then bad "ForOfStatement await"
    else
      pure (.forOfStmt (← decodeLoopHead j) (← decodeExpr (← field j "right"))
        (← decodeStmt (← field j "body")))
  | "SwitchStatement" =>
    pure (.switchStmt (← decodeExpr (← field j "discriminant"))
      (← decodeCases (← arrayField j "cases")))
  | "EmptyStatement" => pure .empty
  | "BlockStatement" => pure (.block (← decodeStmts (← arrayField j "body")))
  | "ThrowStatement" => pure (.throwStmt (← decodeExpr (← field j "argument")))
  | "TryStatement" =>
    let block ← decodeStmts (← blockField j "block")
    let handler ← match ← optField j "handler" with
      | some h => pure (some (← decodeCatch h))
      | none => pure none
    let finalizer ← match ← optField j "finalizer" with
      | some _ => pure (some (← decodeStmts (← blockField j "finalizer")))
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
  | "Unsupported" => throw (.unsupported (← strField j "kind"))
  | other => throw (.unsupported other)

/-- The head of a `for`-`in` or a `for`-`of`. A declaration head is
exactly one declarator with no initializer; `for (var x = 1 in o)` is the
sloppy-mode-only form B.3.5 keeps alive and this epic does not have, and
two declarators do not parse at all. An `ArrayPattern` or `ObjectPattern`
head is an assignment pattern, and every other head is an assignment
target. -/
partial def decodeLoopHead (j : Json) : DecodeM ForInLeft := do
  let head ← field j "left"
  match ← nodeType head with
  | "VariableDeclaration" =>
    let kind ← declKind (← strField head "kind")
    -- The declarator is read here rather than through `declaratorList`
    -- because a *head*'s pattern declarator has no initializer and must
    -- not have one: `for (const [a] of xs)` is the ordinary spelling,
    -- where `const [a];` does not parse at all.
    match (← field head "declarations").getArr? with
    | .ok ds =>
      match ds.toList with
      | [d] =>
        match ← nodeType d with
        | "VariableDeclarator" =>
          match ← optField d "init" with
          | none => pure (.decl kind (← decodePattern true (← field d "id")))
          | some _ => throw (.unsupported "ForInStatement initializer")
        | other => throw (.unsupported other)
      | _ => throw (.unsupported "ForInStatement initializer")
    | .error _ => bad "VariableDeclaration declarations is not an array"
  | "ArrayPattern" | "ObjectPattern" => pure (.pattern (← decodePattern false head))
  | _ => pure (.target (← toTarget (← decodeExpr head)))

/-- A `CatchClause`. The parameter is a binding pattern, and an
out-of-slice one is refused in place — the clause, and so the `try`
around it, survives — which is the precedent a function parameter set. -/
partial def decodeCatch (j : Json) : DecodeM CatchClause := do
  let param ← match ← optField j "param" with
    | none => pure none
    | some p => pure (some (← decodePattern true p))
  pure { param, body := ← decodeStmts (← blockField j "body") }

/-- A `VariableDeclaration`'s declarators, in a statement or in a `for`
head. Both spellings refuse an empty list the same way: an engine cannot
parse one, so a document with one is a broken producer. -/
partial def declaratorList (j : Json) : DecodeM (List Declarator) := do
  match (← field j "declarations").getArr? with
  | .error _ => bad "VariableDeclaration declarations is not an array"
  | .ok ds =>
    if ds.isEmpty then bad "VariableDeclaration has no declarators"
    else decodeDeclarators ds.toList

partial def decodeDeclarators : List Json → DecodeM (List Declarator)
  | [] => pure []
  | d :: rest => do pure ((← decodeDeclarator d) :: (← decodeDeclarators rest))

/-- A `switch`'s clauses. A `default` clause has a null `test`; anything
in the list that is not a `SwitchCase` is a broken producer, since the
bridge has no other node to put there. -/
partial def decodeCases : List Json → DecodeM (List SwitchCase)
  | [] => pure []
  | c :: rest => do
    match ← nodeType c with
    | "SwitchCase" =>
      let test ← optExpr c "test"
      pure ({ test, body := ← decodeStmts (← arrayField c "consequent") } :: (← decodeCases rest))
    | other => bad s!"switch case is a {other}"

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
private def decodeProgramM (j : Json) : DecodeM Program := do
  match ← nodeType j with
  | "Program" => pure ()
  | other => throw (.unsupported other)
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
          throw (.unsupported "Directive")
        else decodeStmts rest

/-- Decode a whole document, starting the template-site counter at zero.
The signature is `Except`, not `DecodeM`: the state is the decoder's own
bookkeeping and no caller has anything to say about it. -/
def decodeProgram (j : Json) : Except DecodeError Program :=
  (decodeProgramM j).run' 0

end Tarski
