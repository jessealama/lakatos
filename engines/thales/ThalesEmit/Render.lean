import Lean
import ThalesDsl
import ThalesEmit.Json

/-! IR → `TSyntax` → text. Every line of Lean code in the artifact is
built by quotation and printed by Lean's pretty-printer; the only strings
assembled by hand are comments and the fixed header. Shapes beyond this
slice — module-qualified names — are refused with a message naming the
gap, never approximated. -/

namespace ThalesEmit

open Lean

/-- Syntax is built unhygienically — the artifact is plain text, so the
identifiers must print exactly as a person would write them. -/
abbrev RenderM := ExceptT String Unhygienic

def RenderM.run {α : Type} (x : RenderM α) : Except String α :=
  Unhygienic.run (ExceptT.run x)

partial def numTerm (lit : String) : RenderM (TSyntax `term) := do
  if lit == "Infinity" then `(floatInf)
  else if lit.startsWith "-" then
    let inner ← numTerm (lit.drop 1).toString
    `(-$inner)
  else if lit.any (fun c => c == '.' || c == 'e') then
    pure ⟨Syntax.mkScientificLit lit⟩
  else
    pure ⟨Syntax.mkNumLit lit⟩

/-- A plain identifier. The IR's names come from TypeScript identifiers,
which are Lean-atomic; anything else (a module-qualified closure name)
waits for its slice. -/
def identTerm (name : String) : RenderM Ident := do
  unless name.length > 0 && name.front.isAlpha &&
      name.all (fun c => c.isAlphanum || c == '_') do
    throw s!"'{name}' is not an emittable identifier yet"
  return mkIdent (Name.mkSimple name)

/-- The names the emitted text references unqualified. The artifact is
re-parsed plain text, so a binder or parameter spelled like one would
capture the reference. -/
def reservedNames : List String :=
  ["pure", "ballIco", "floatInf", "Float", "Number", "Int",
   "JsM", "JsNumber", "Bool", "TsModel", "JsError", "mut"]

/-- A binder or parameter: the source name, primed out of the reserved
vocabulary — a spelling no TS identifier has. -/
def scopedIdent (name : String) : RenderM Ident := do
  let _ ← identTerm name
  if reservedNames.contains name then
    return mkIdent (Name.mkSimple (name ++ "'"))
  return mkIdent (Name.mkSimple name)

/-- A model reference: emitted defs live under the old pipeline's
`TsModel` namespace, so they collide with no root-level name and no
binder can capture them. -/
def modelIdent (name : String) : RenderM Ident := do
  let _ ← identTerm name
  return mkIdent (`TsModel ++ Name.mkSimple name)

/-- A value-level rendering: a Float- or Bool-valued term that may embed
`(← call)` lifts, and whether any lift occurred. Lifts appear left to
right in JS evaluation order, which is the old model's bind order. -/
structure Rendered where
  term : TSyntax `term
  lifted : Bool

mutual

/-- `coerced` names the Int-valued binder variables: a use inside an
obligation body crosses to the Float world as `Float.ofInt x`, the same
boundary the old pipeline's binders cross. -/
partial def valueTerm (coerced : String → Bool) : JsExpr → RenderM Rendered
  | .num lit => return ⟨← numTerm lit, false⟩
  | .id name => do
    let x ← scopedIdent name
    if coerced name then return ⟨← `(Float.ofInt $x), false⟩
    return ⟨x, false⟩
  | .unop op x => do
    let ⟨t, lifted⟩ ← valueTerm coerced x
    match op with
    | "-" => return ⟨← `(-$t), lifted⟩
    -- Unary plus is ToNumber on a value already a number: the identity.
    | "+" => return ⟨t, lifted⟩
    | _ => throw s!"unary operator '{op}' is not in the emission slice yet"
  | .binop op l r => do
    let ⟨lt, ll⟩ ← valueTerm coerced l
    let ⟨rt, rl⟩ ← valueTerm coerced r
    let lifted := ll || rl
    -- `>`/`>=` flip their operands; when both sides carry effects the
    -- flip is applied through a lambda so the lifts still elaborate in
    -- JS evaluation order.
    let flipped (f : TSyntax `term → TSyntax `term → RenderM (TSyntax `term)) :
        RenderM Rendered := do
      if ll && rl then
        let a := mkIdent (Name.mkSimple "a")
        let b := mkIdent (Name.mkSimple "b")
        return ⟨← `((fun $a $b => $(← f b a)) $lt $rt), lifted⟩
      return ⟨← f rt lt, lifted⟩
    match op with
    | "+" => return ⟨← `($lt + $rt), lifted⟩
    | "-" => return ⟨← `($lt - $rt), lifted⟩
    | "*" => return ⟨← `($lt * $rt), lifted⟩
    | "/" => return ⟨← `($lt / $rt), lifted⟩
    | "%" => return ⟨← `(Number.FloatOps.tsRem $lt $rt), lifted⟩
    | "<" => return ⟨← `(Float.lt $lt $rt), lifted⟩
    | "<=" => return ⟨← `(Float.le $lt $rt), lifted⟩
    | ">" => flipped fun x y => `(Float.lt $x $y)
    | ">=" => flipped fun x y => `(Float.le $x $y)
    | "===" => return ⟨← `(Float.beq $lt $rt), lifted⟩
    | "!==" => return ⟨← `(!Float.beq $lt $rt), lifted⟩
    | _ => throw s!"operator '{op}' is not in the emission slice yet"
  | .call callee args => do
    let c ← callTerm coerced callee args
    return ⟨← `((← $c:term)), true⟩

/-- A call as the `JsM` value it denotes, its arguments still
value-level. -/
partial def callTerm (coerced : String → Bool) (callee : String)
    (args : Array JsExpr) : RenderM (TSyntax `term) := do
  let f ← modelIdent callee
  let argTerms ← args.mapM (fun a => return (← valueTerm coerced a).term)
  if argTerms.isEmpty then pure f else `($f $argTerms*)

end

/-- A `JsM`-valued rendering of an expression, for the sides of an
equation: a bare call stays the call (and pins the monad for the other
side), anything else lifts with `pure` or a `do return`. The flag says
whether the term pins `JsM` on its own. -/
def monadicTerm (coerced : String → Bool) :
    JsExpr → RenderM (TSyntax `term × Bool)
  | .call callee args => do
    let liftedArgs ← args.anyM fun a =>
      return (← valueTerm coerced a).lifted
    if liftedArgs then
      let ⟨t, _⟩ ← valueTerm coerced (.call callee args)
      return (← `(do return $t), false)
    return (← callTerm coerced callee args, true)
  | e => do
    let ⟨t, lifted⟩ ← valueTerm coerced e
    if lifted then return (← `(do return $t), false)
    return (← `(pure $t), false)

def intEndpointTerm (i : Int) : RenderM (TSyntax `term) := do
  let n : TSyntax `term := ⟨Syntax.mkNumLit (toString i.natAbs)⟩
  if i < 0 then `(-$n) else pure n

/-! Statement bodies render as do-notation — `let`, `let mut`, `if`
statements, early `return`, `throw` — one Lean statement per IR statement:
the do-elaborator does the control-flow lowering, so no tail is ever
written out twice and no helper lambda reaches the source text. -/

/-- A statement's value expression: binder-coercion never applies inside a
body, where every name is already a `JsNumber`. -/
def bodyTerm (e : JsExpr) : RenderM (TSyntax `term) :=
  return (← valueTerm (fun _ => false) e).term

mutual

/-- An arm's statement sequence. An arm the source left empty still needs
a do-element, so it renders as `pure ()`. -/
partial def stmtsDoSeq (stmts : Array JsStmt) :
    RenderM (TSyntax ``Lean.Parser.Term.doSeqIndent) := do
  let elems ←
    if stmts.isEmpty then pure #[← `(doElem| pure ())]
    else stmts.mapM stmtDoElem
  `(Lean.Parser.Term.doSeqIndent| $[$elems:doElem]*)

partial def stmtDoElem : JsStmt → RenderM (TSyntax `doElem)
  | .ret e => do `(doElem| return $(← bodyTerm e))
  | .throwErr kind =>
    -- The error carries its constructor name alone, like the old model.
    `(doElem| throw (JsError.error $(Syntax.mkStrLit kind)))
  | .constDecl x e => do
    -- Locals are ascribed: TypeScript typed them `number`, and a bare
    -- literal initializer would otherwise elaborate at `Nat`.
    `(doElem| let $(← scopedIdent x) : JsNumber := $(← bodyTerm e))
  | .letDecl x e => do
    `(doElem| let mut $(← scopedIdent x) : JsNumber := $(← bodyTerm e))
  | .assign x e => do
    `(doElem| $(← scopedIdent x):ident := $(← bodyTerm e))
  | .ite c thn els => iteElem c thn els

/-- An `if` statement. An else arm that is itself exactly one `if` joins
the chain as `else if`, the way the source spells it: the nested doIf's
condition and arms are grafted onto the outer node's else-if groups,
which is syntax the quotations built — only rearranged. -/
partial def iteElem (c : JsExpr) (thn : Array JsStmt)
    (els : Option (Array JsStmt)) : RenderM (TSyntax `doElem) := do
  let ct ← bodyTerm c
  let thenSeq ← stmtsDoSeq thn
  match els with
  | none => `(doElem| if $ct then $thenSeq:doSeqIndent)
  | some #[.ite c2 t2 e2] => do
    let inner ← iteElem c2 t2 e2
    let base ← `(doElem| if $ct then $thenSeq:doSeqIndent)
    -- doIf's shape: "if", cond, "then", seq, else-if groups, else?.
    let a := inner.raw.getArgs
    let elseIf := mkNode `group
      #[mkNode `group #[mkAtom "else", mkAtom "if"], a[1]!, a[2]!, a[3]!]
    return ⟨(base.raw.setArg 4 (mkNullNode (#[elseIf] ++ a[4]!.getArgs))).setArg 5 a[5]!⟩
  | some elseStmts => do
    let elseSeq ← stmtsDoSeq elseStmts
    `(doElem| if $ct then $thenSeq:doSeqIndent else $elseSeq:doSeqIndent)

end

/-- The mutable names a statement tree assigns, arms included: a parameter
among them is rebound `let mut` ahead of the body, the way JavaScript has
parameters assignable. -/
partial def assignedNames (s : JsStmt) : List String :=
  match s with
  | .assign x _ => [x]
  | .ite _ thn els =>
    thn.toList.flatMap assignedNames
      ++ (els.getD #[]).toList.flatMap assignedNames
  | _ => []

def fnCommand (f : EmitFn) : RenderM (TSyntax `command) := do
  let name ← modelIdent f.name
  let params ← f.params.mapM scopedIdent
  let assigned := f.body.toList.flatMap assignedNames
  let rebound ← f.params.filterMapM fun p => do
    unless assigned.contains p do return none
    let pi ← scopedIdent p
    return some (← `(doElem| let mut $pi:ident := $pi))
  let body ← f.body.mapM stmtDoElem
  let elems := rebound ++ body
  -- Dual-tagged like the old models: the js_norm closers and the grind
  -- rung both unfold a model by its equations.
  `(@[js_norm, grind] def $name ($params* : JsNumber) : JsM JsNumber := do
      $[$elems:doElem]*)

/-- A boolean-valued expression as the proposition that it evaluates to
`pure true` — the shape the old pipeline elaborates for both a boolean
island conclusion and a guard hypothesis. -/
def boolIsland (coerced : String → Bool) (expr : JsExpr) :
    RenderM (TSyntax `term) := do
  let ⟨t, lifted⟩ ← valueTerm coerced expr
  if lifted then `(((do return $t) : JsM Bool) = pure true)
  else `((pure $t : JsM Bool) = pure true)

def obligationCommand (e : Emission) (o : Obligation) : RenderM (TSyntax `command) := do
  let file := Syntax.mkStrLit e.file
  let fn := Syntax.mkStrLit o.function
  let prop := Syntax.mkStrLit o.property
  match o.payload with
  | .bare => `(#thales_prove $file $fn $prop)
  | .structured binders guards conclusion =>
    -- Only the Int-enumerated binders coerce; a `number` binder is already
    -- a double, the way the old pipeline's Float ∀ is.
    let bound := (binders.filter (·.isIntValued)).map (·.name)
    let coerced := fun n => bound.contains n
    let leaf ← match conclusion with
      | .eq l r => do
        let (lt, lPins) ← monadicTerm coerced l
        let (rt, rPins) ← monadicTerm coerced r
        -- `≡` is SameValue, which is exactly propositional equality on
        -- `JsM` results. A side that is a bare call pins the monad; with
        -- neither, the left side is ascribed.
        if lPins || rPins then `($lt = $rt)
        else `(($lt : JsM JsNumber) = $rt)
      | .istrue expr => boolIsland coerced expr
    -- A guard is a hypothesis, not a connective: one that throws fails it
    -- just as one that returns false does, excluding the assignment.
    let leaf ← guards.foldrM (init := leaf) fun g acc => do
      `($(← boolIsland coerced g) → $acc)
    let propTerm ← binders.foldrM (init := leaf) fun b acc => do
      match b with
      | .range name lo hi =>
        let xi ← scopedIdent name
        `(ballIco $(← intEndpointTerm lo) $(← intEndpointTerm hi) fun $xi => $acc)
      | .int name =>
        let xi ← scopedIdent name
        `(∀ ($xi : Int), $acc)
      | .nat name =>
        let xi ← scopedIdent name
        `(∀ ($xi : Int), 0 ≤ $xi → $acc)
      | .number name lower upper =>
        -- Never enumerated: the binder is its type plus whichever bounds it
        -- carries as hypotheses, lower outermost — the old pipeline's shape.
        -- One ungrouped ∀ head per binder, never `∀ (x y : JsNumber)`: that
        -- is the only spelling `ProveTerm.propSpine` recovers.
        let xi ← scopedIdent name
        let mut body := acc
        if let some (op, lit) := upper then
          let e ← numTerm lit
          body ← match op with
            | "<" => `($xi < $e → $body)
            | "<=" => `($xi ≤ $e → $body)
            | _ => throw s!"unsupported upper bound '{op}'"
        if let some (op, lit) := lower then
          let e ← numTerm lit
          body ← match op with
            | "<" => `($e < $xi → $body)
            | "<=" => `($e ≤ $xi → $body)
            | _ => throw s!"unsupported lower bound '{op}'"
        `(∀ ($xi : JsNumber), $body)
    `(#thales_prove $file $fn $prop := $propTerm:term)

/-- The artifact's fixed header: scaffolding, not code the printer owns.
`autoImplicit` is pinned off because artifacts run under lean's defaults,
where an unbound identifier would auto-bind instead of erroring. -/
def header (e : Emission) : String :=
  s!"-- generated by thales-emit from {e.file}\n" ++
  "import ThalesDsl\n\n" ++
  "open Js ThalesDsl\n\n" ++
  "set_option autoImplicit false"

def commentLines (text : String) : String :=
  String.intercalate "\n"
    ((text.splitOn "\n").map fun line =>
      if line.isEmpty then "--" else s!"-- {line}")

/-- `Unhygienic` still stamps its one macro scope on quotation-literal
identifiers, which the printer would flag with `✝`; the artifact is
plain text, so the scopes are erased before printing. -/
partial def unscope : Syntax → Syntax
  | .ident info rawVal val preresolved =>
    .ident info rawVal val.eraseMacroScopes preresolved
  | .node info kind args => .node info kind (args.map unscope)
  | s => s

def indentWidth (line : String) : Nat := (line.takeWhile (· == ' ')).toString.length

/-- `return`'s argument is optional, so a line break between the two parses
back as a bare `return`; the printer breaks there whenever the argument is
too wide for the line. Rejoining them is what keeps the artifact
re-parsable. A broken argument is always indented past its `return`, which
is what tells it apart from a genuinely bare `return` followed by a
sibling statement. -/
partial def joinReturns : List String → List String
  | line :: rest =>
    match joinReturns rest with
    | next :: tail =>
      if (line == "return" || line.endsWith " return") &&
          indentWidth next > indentWidth line then
        (line ++ " " ++ next.dropWhile (· == ' ')) :: tail
      else line :: next :: tail
    | [] => [line]
  | [] => []

/-- Formatted command text, without trailing whitespace: the printer
leaves a dangling space after `then` when the arm breaks to its own line,
and the artifact is plain text a person's editor would flag it in. -/
def prettyLines (fmt : Format) : String :=
  String.intercalate "\n"
    (joinReturns
      (((fmt.pretty 100).splitOn "\n").map (·.dropEndWhile (· == ' ') |>.toString)))

/-- The full artifact text. Pretty-printing runs in `CoreM` against an
environment that imports `ThalesDsl`, which carries every syntax the
quotations build. -/
def renderEmission (e : Emission) : CoreM String := do
  let mut blocks : Array String := #[header e]
  for f in e.declarations do
    let cmd ← rendered (fnCommand f)
    blocks := blocks.push
      (commentLines f.source ++ "\n" ++ prettyLines (← ppCommand cmd))
  for o in e.obligations do
    let cmd ← rendered (obligationCommand e o)
    blocks := blocks.push
      (s!"-- @ensures\{{o.property}} {o.formula}\n" ++ prettyLines (← ppCommand cmd))
  return String.intercalate "\n\n" blocks.toList ++ "\n"
where
  rendered (x : RenderM (TSyntax `command)) : CoreM (TSyntax `command) := do
    match RenderM.run x with
    | .error msg => throwError msg
    | .ok cmd => pure cmd
  ppCommand (cmd : TSyntax `command) : CoreM Format :=
    PrettyPrinter.ppCommand ⟨unscope cmd.raw⟩

end ThalesEmit
