import ThalesEmit.Render

/-! `Tarski.Program` → a Lean term, by quotation.

What a declaration carries is the *decoder's* reading of the bridge's
ESTree, so this file's whole job is to spell a `Tarski.Program` value back
as text: the artifact's `TsModel.f.ast` is then what the evaluator would
run, not the emitter's own reading of `f`. It is total — one arm per
constructor — because a shape it skipped would be a program the artifact
claims to carry and does not.

Dot-constructor notation throughout. The def the term lands in ascribes
`Tarski.Program`, so every constructor elaborates against the expected
type and prints as a person would write it, and a plain parameter prints
as its name through `Coe String Param`.

Numbers go through `Js.Number.toDecimalString`, ECMA's `Number::toString`,
and then through `numTerm`: that is the one spelling a JS literal, the
bridge's JSON, the decoder, and a Lean literal already share, so the
printed literal has the input's bits. -/

namespace ThalesEmit

open Lean

/-- A constructor in dot notation. The name is one `Name` component, and
Lean's printer does not escape a component that is a keyword — `toString`
escapes what is not identifier-*shaped* — so a constructor `Tarski/Ast.lean`
itself spells between guillemets carries them inside the component, the
idiom `fieldIdent` uses for a `#`-spelled field. -/
def dotCtor (name : String) : Term :=
  ⟨Syntax.node .none ``Lean.Parser.Term.dotIdent
    #[Syntax.atom .none ".", mkIdent (Name.mkSimple name)]⟩

/-- A constructor applied to its arguments; a nullary one is the dot
ident alone. -/
def ctorApp (name : String) (args : Array Term) : RenderM Term := do
  let f := dotCtor name
  if args.isEmpty then pure f else `($f $args*)

/-- Every name in the AST — an identifier, a label, a property, a
parameter — is a `String` field, so it prints as a string literal. -/
def strTerm (s : String) : Term := ⟨Syntax.mkStrLit s⟩

def boolTerm (b : Bool) : RenderM Term := if b then `(true) else `(false)

/-- `some x` or `none`, the one spelling every optional field takes. -/
def optTerm (t? : Option Term) : RenderM Term :=
  match t? with
  | none => `(none)
  | some t => `(some $t)

/-- A template's cooked strings, one more of them than its substitutions. -/
def strsTerm (ss : List String) : RenderM Term :=
  let xs := ss.toArray.map strTerm
  `([$xs,*])

/-- A tagged template's site number, the decoder's index for its Parse
Node, as a numeral. -/
def natTerm (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩

/-- A string literal's value. A `Tarski.Expr.strLit` carries a
`Js.JsString` — a sequence of UTF-16 code units — so a string that names a
Lean `String` prints as that literal and elaborates back through
`Coe String JsString`, and one with an unpaired surrogate, which no Lean
`String` can hold, prints as its code units. -/
def jsStringTerm (s : Js.JsString) : RenderM Term :=
  match Js.JsString.asString? s with
  | some str => pure (strTerm str)
  | none =>
    let xs := s.units.toArray.map (fun u => natTerm u.toNat)
    `(Js.JsString.mk [$xs,*])

/-- One `TemplateString` of a tagged template: its cooked value, `none`
for a raw text the cooked grammar refuses, beside the raw text. -/
def templateStringTerm (s : Tarski.TemplateString) : RenderM Term := do
  let cooked ← optTerm (s.cooked.map strTerm)
  `({ cooked := $cooked, raw := $(strTerm s.raw) })

def templateStringsTerm (ss : List Tarski.TemplateString) : RenderM Term := do
  let xs ← ss.toArray.mapM templateStringTerm
  `([$xs,*])

/-- A `Float` as the literal whose bits it has: `Number::toString`'s
answer, read back by `numTerm` — `Infinity` and `NaN` as the library's
constants, a leading `-` as a negation, anything with a point or an
exponent as a scientific literal. -/
def floatTerm (x : Float) : RenderM Term :=
  numTerm (Js.Number.toDecimalString x)

def declKindTerm : Tarski.DeclKind → Term
  | .«let» => dotCtor "«let»"
  | .«const» => dotCtor "«const»"
  | .«var» => dotCtor "«var»"

def unaryOpTerm : Tarski.UnaryOp → Term
  | .neg => dotCtor "neg"
  | .plus => dotCtor "plus"
  | .not => dotCtor "not"
  | .typeof => dotCtor "typeof"
  | .void => dotCtor "void"

def binaryOpTerm : Tarski.BinaryOp → Term
  | .add => dotCtor "add"
  | .sub => dotCtor "sub"
  | .mul => dotCtor "mul"
  | .div => dotCtor "div"
  | .rem => dotCtor "rem"
  | .exponent => dotCtor "exponent"
  | .lt => dotCtor "lt"
  | .le => dotCtor "le"
  | .gt => dotCtor "gt"
  | .ge => dotCtor "ge"
  | .strictEq => dotCtor "strictEq"
  | .strictNe => dotCtor "strictNe"
  | .instanceof => dotCtor "instanceof"
  | .«in» => dotCtor "«in»"

def logicalOpTerm : Tarski.LogicalOp → Term
  | .and => dotCtor "and"
  | .or => dotCtor "or"

def updateOpTerm : Tarski.UpdateOp → Term
  | .inc => dotCtor "inc"
  | .dec => dotCtor "dec"

def methodKindTerm : Tarski.MethodKind → Term
  | .method => dotCtor "method"
  | .getter => dotCtor "getter"
  | .setter => dotCtor "setter"

def classKeyTerm : Tarski.ClassKey → RenderM Term
  | .«public» name => ctorApp "«public»" #[strTerm name]
  | .«private» name => ctorApp "«private»" #[strTerm name]

mutual

partial def exprTerm : Tarski.Expr → RenderM Term
  | .numLit value => do ctorApp "numLit" #[← floatTerm value]
  | .strLit value => do ctorApp "strLit" #[← jsStringTerm value]
  | .boolLit value => do ctorApp "boolLit" #[← boolTerm value]
  | .undefLit => ctorApp "undefLit" #[]
  | .nullLit => ctorApp "nullLit" #[]
  | .ident name => ctorApp "ident" #[strTerm name]
  | .this => ctorApp "this" #[]
  | .unary op operand => do
    ctorApp "unary" #[unaryOpTerm op, ← exprTerm operand]
  | .binary op left right => do
    ctorApp "binary" #[binaryOpTerm op, ← exprTerm left, ← exprTerm right]
  | .logical op left right => do
    ctorApp "logical" #[logicalOpTerm op, ← exprTerm left, ← exprTerm right]
  | .cond test consequent alternate => do
    ctorApp "cond"
      #[← exprTerm test, ← exprTerm consequent, ← exprTerm alternate]
  | .member object name => do
    ctorApp "member" #[← exprTerm object, strTerm name]
  | .index object key => do
    ctorApp "index" #[← exprTerm object, ← exprTerm key]
  | .privateMember object name => do
    ctorApp "privateMember" #[← exprTerm object, strTerm name]
  | .superMember name => ctorApp "superMember" #[strTerm name]
  | .superIndex key => do ctorApp "superIndex" #[← exprTerm key]
  | .superCall args => do ctorApp "superCall" #[← exprsTerm args]
  | .call callee args => do
    ctorApp "call" #[← exprTerm callee, ← exprsTerm args]
  | .new callee args => do
    ctorApp "new" #[← exprTerm callee, ← exprsTerm args]
  | .arrayLit elements => do ctorApp "arrayLit" #[← exprsTerm elements]
  | .objectLit props => do ctorApp "objectLit" #[← propsTerm props]
  | .template strings exprs => do
    ctorApp "template" #[← strsTerm strings, ← exprsTerm exprs]
  | .taggedTemplate tag site strings exprs => do
    ctorApp "taggedTemplate"
      #[← exprTerm tag, natTerm site, ← templateStringsTerm strings, ← exprsTerm exprs]
  | .funcExpr name params body => do
    ctorApp "funcExpr"
      #[← optTerm (name.map strTerm), ← paramsTerm params, ← stmtsTerm body]
  | .arrow params body => do
    ctorApp "arrow" #[← paramsTerm params, ← arrowBodyTerm body]
  | .assign target value => do
    ctorApp "assign" #[← targetTerm target, ← exprTerm value]
  | .compoundAssign op target value => do
    ctorApp "compoundAssign"
      #[binaryOpTerm op, ← targetTerm target, ← exprTerm value]
  | .update op isPrefix target => do
    ctorApp "update"
      #[updateOpTerm op, ← boolTerm isPrefix, ← targetTerm target]
  | .classExpr cls => do ctorApp "classExpr" #[← classDefTerm cls]
  | .delete operand => do ctorApp "delete" #[← exprTerm operand]
  | .assignPattern pattern value => do
    ctorApp "assignPattern" #[← patternTerm pattern, ← exprTerm value]
  | .spread argument => do ctorApp "spread" #[← exprTerm argument]
  | .hole => ctorApp "hole" #[]

partial def exprsTerm (es : List Tarski.Expr) : RenderM Term := do
  let xs ← es.toArray.mapM exprTerm
  `([$xs,*])

/-- A property key: a written name, or the expression a computed key
(and a numeric literal key) evaluates through ToPropertyKey. -/
partial def propKeyTerm : Tarski.PropKey → RenderM Term
  | .name s => ctorApp "name" #[strTerm s]
  | .computed e => do ctorApp "computed" #[← exprTerm e]

/-- One object-literal member: a key-and-value pair (a shorthand is one
whose value is its own name), a method or accessor, or the `__proto__:`
form. -/
partial def propDefTerm : Tarski.PropDef → RenderM Term
  | .init key value => do ctorApp "init" #[← propKeyTerm key, ← exprTerm value]
  | .method kind key params body => do
    ctorApp "method"
      #[methodKindTerm kind, ← propKeyTerm key, ← paramsTerm params, ← stmtsTerm body]
  | .proto value => do ctorApp "proto" #[← exprTerm value]
  | .spread value => do ctorApp "spread" #[← exprTerm value]

/-- An object literal's members, in the source order the AST keeps. -/
partial def propsTerm (ps : List Tarski.PropDef) : RenderM Term := do
  let xs ← ps.toArray.mapM propDefTerm
  `([$xs,*])

partial def targetTerm : Tarski.Target → RenderM Term
  | .ident name => ctorApp "ident" #[strTerm name]
  | .member object name => do
    ctorApp "member" #[← exprTerm object, strTerm name]
  | .index object key => do
    ctorApp "index" #[← exprTerm object, ← exprTerm key]
  | .privateMember object name => do
    ctorApp "privateMember" #[← exprTerm object, strTerm name]

partial def arrowBodyTerm : Tarski.ArrowBody → RenderM Term
  | .expr value => do ctorApp "expr" #[← exprTerm value]
  | .block body => do ctorApp "block" #[← stmtsTerm body]

/-- A pattern. A plain identifier leaf prints as its name — `Coe String
Pattern` is what makes that elaborate — and every other shape as the
constructor or structure it is. -/
partial def patternTerm : Tarski.Pattern → RenderM Term
  | .target (.ident name) => pure (strTerm name)
  | .target t => do ctorApp "target" #[← targetTerm t]
  | .array elements rest => do
    ctorApp "array"
      #[← patternElemsTerm elements, ← optTerm (← rest.mapM patternTerm)]
  | .object props rest => do
    ctorApp "object"
      #[← patternPropsTerm props, ← optTerm (← rest.mapM targetTerm)]

/-- One `ArrayPattern` element. -/
partial def patternElemTerm (e : Tarski.PatternElem) : RenderM Term := do
  let target ← patternTerm e.target
  let dflt ← optTerm (← e.default.mapM exprTerm)
  `({ target := $target, default := $dflt })

/-- An `ArrayPattern`'s elements, `none` being an elision. -/
partial def patternElemsTerm (es : List (Option Tarski.PatternElem)) :
    RenderM Term := do
  let xs ← es.toArray.mapM (fun e => do optTerm (← e.mapM patternElemTerm))
  `([$xs,*])

/-- One `ObjectPattern` property. -/
partial def patternPropTerm (p : Tarski.PatternProp) : RenderM Term := do
  let key ← propKeyTerm p.key
  let target ← patternTerm p.target
  let dflt ← optTerm (← p.default.mapM exprTerm)
  `({ key := $key, target := $target, default := $dflt })

/-- An `ObjectPattern`'s properties, in source order. -/
partial def patternPropsTerm (ps : List Tarski.PatternProp) : RenderM Term := do
  let xs ← ps.toArray.mapM patternPropTerm
  `([$xs,*])

/-- A plain parameter is its name as a string literal — `Coe String Param`
is what makes that elaborate — and a defaulted, destructuring, or rest
one is the structure it is, `rest` printed only when it is set. -/
partial def paramTerm (p : Tarski.Param) : RenderM Term := do
  match p.target, p.default, p.rest with
  | .target (.ident name), none, false => pure (strTerm name)
  | _, _, _ =>
    let target ← patternTerm p.target
    let dflt ← optTerm (← p.default.mapM exprTerm)
    if p.rest then `({ target := $target, default := $dflt, rest := true })
    else `({ target := $target, default := $dflt })

partial def paramsTerm (ps : List Tarski.Param) : RenderM Term := do
  let xs ← ps.toArray.mapM paramTerm
  `([$xs,*])

partial def declaratorTerm (d : Tarski.Declarator) : RenderM Term := do
  let target ← patternTerm d.target
  let init ← optTerm (← d.init.mapM exprTerm)
  `({ target := $target, init := $init })

partial def declaratorsTerm (ds : List Tarski.Declarator) : RenderM Term := do
  let xs ← ds.toArray.mapM declaratorTerm
  `([$xs,*])

partial def forInitTerm : Tarski.ForInit → RenderM Term
  | .decl kind declarators => do
    ctorApp "decl" #[declKindTerm kind, ← declaratorsTerm declarators]
  | .expr value => do ctorApp "expr" #[← exprTerm value]

partial def forInLeftTerm : Tarski.ForInLeft → RenderM Term
  | .decl kind target => do ctorApp "decl" #[declKindTerm kind, ← patternTerm target]
  | .target t => do ctorApp "target" #[← targetTerm t]
  | .pattern p => do ctorApp "pattern" #[← patternTerm p]

partial def switchCaseTerm (c : Tarski.SwitchCase) : RenderM Term := do
  let test ← optTerm (← c.test.mapM exprTerm)
  let body ← stmtsTerm c.body
  `({ test := $test, body := $body })

partial def casesTerm (cs : List Tarski.SwitchCase) : RenderM Term := do
  let xs ← cs.toArray.mapM switchCaseTerm
  `([$xs,*])

partial def catchTerm (c : Tarski.CatchClause) : RenderM Term := do
  let param ← optTerm (← c.param.mapM patternTerm)
  let body ← stmtsTerm c.body
  `({ param := $param, body := $body })

partial def elementTerm : Tarski.ClassElement → RenderM Term
  | .ctor params body => do
    ctorApp "ctor" #[← paramsTerm params, ← stmtsTerm body]
  | .method kind isStatic name params body => do
    ctorApp "method"
      #[methodKindTerm kind, ← boolTerm isStatic, strTerm name,
        ← paramsTerm params, ← stmtsTerm body]
  | .field isStatic key value => do
    ctorApp "field"
      #[← boolTerm isStatic, ← classKeyTerm key,
        ← optTerm (← value.mapM exprTerm)]

partial def elementsTerm (es : List Tarski.ClassElement) : RenderM Term := do
  let xs ← es.toArray.mapM elementTerm
  `([$xs,*])

partial def classDefTerm (d : Tarski.ClassDef) : RenderM Term := do
  let name ← optTerm (d.name.map strTerm)
  let superClass ← optTerm (← d.superClass.mapM exprTerm)
  let elements ← elementsTerm d.elements
  `({ name := $name, superClass := $superClass, elements := $elements })

partial def stmtTerm : Tarski.Stmt → RenderM Term
  | .exprStmt value => do ctorApp "exprStmt" #[← exprTerm value]
  | .varDecl kind declarators => do
    ctorApp "varDecl" #[declKindTerm kind, ← declaratorsTerm declarators]
  | .funcDecl name params body => do
    ctorApp "funcDecl"
      #[strTerm name, ← paramsTerm params, ← stmtsTerm body]
  | .returnStmt argument => do
    ctorApp "returnStmt" #[← optTerm (← argument.mapM exprTerm)]
  | .ifStmt test consequent alternate => do
    ctorApp "ifStmt"
      #[← exprTerm test, ← stmtTerm consequent,
        ← optTerm (← alternate.mapM stmtTerm)]
  | .whileStmt test body => do
    ctorApp "whileStmt" #[← exprTerm test, ← stmtTerm body]
  | .doWhileStmt body test => do
    ctorApp "doWhileStmt" #[← stmtTerm body, ← exprTerm test]
  | .forStmt init test update body => do
    ctorApp "forStmt"
      #[← optTerm (← init.mapM forInitTerm),
        ← optTerm (← test.mapM exprTerm),
        ← optTerm (← update.mapM exprTerm),
        ← stmtTerm body]
  | .switchStmt discriminant cases => do
    ctorApp "switchStmt" #[← exprTerm discriminant, ← casesTerm cases]
  | .empty => ctorApp "empty" #[]
  | .block body => do ctorApp "block" #[← stmtsTerm body]
  | .throwStmt argument => do ctorApp "throwStmt" #[← exprTerm argument]
  | .tryStmt block handler finalizer => do
    ctorApp "tryStmt"
      #[← stmtsTerm block,
        ← optTerm (← handler.mapM catchTerm),
        ← optTerm (← finalizer.mapM stmtsTerm)]
  | .labeled label body => do
    ctorApp "labeled" #[strTerm label, ← stmtTerm body]
  | .breakStmt label => do
    ctorApp "breakStmt" #[← optTerm (label.map strTerm)]
  | .continueStmt label => do
    ctorApp "continueStmt" #[← optTerm (label.map strTerm)]
  | .forInStmt left right body => do
    ctorApp "forInStmt"
      #[← forInLeftTerm left, ← exprTerm right, ← stmtTerm body]
  | .forOfStmt left right body => do
    ctorApp "forOfStmt"
      #[← forInLeftTerm left, ← exprTerm right, ← stmtTerm body]
  | .classDecl name cls => do
    ctorApp "classDecl" #[strTerm name, ← classDefTerm cls]

partial def stmtsTerm (ss : List Tarski.Stmt) : RenderM Term := do
  let xs ← ss.toArray.mapM stmtTerm
  `([$xs,*])

end

/-- A whole program: the statement list the decoder answered with, its
`"use strict"` directive already consumed. -/
def programTerm (p : Tarski.Program) : RenderM Term := stmtsTerm p

/-- The declaration's AST def sits one component below the declaration's
own model name, which is why `ast` is a reserved member spelling. -/
def astIdent (base : Ident) : Ident := mkIdent (base.getId ++ `ast)

/-- The def a decoded closure prints as. No attribute: nothing unfolds it
in a proof, and #481's command names it. -/
def astCommand (name : Ident) (p : Tarski.Program) :
    RenderM (TSyntax `command) := do
  let body ← programTerm p
  `(def $name : Tarski.Program := $body)

end ThalesEmit
