import Lean
import ThalesDsl
import ThalesEmit.Json

/-! IR → `TSyntax` → text. Every line of Lean code in the artifact is
built by quotation and printed by Lean's pretty-printer; the only strings
assembled by hand are comments and the fixed header. Shapes beyond this
slice are refused with a message naming the gap, never approximated. -/

namespace ThalesEmit

open Lean

/-- Syntax is built unhygienically — the artifact is plain text, so the
identifiers must print exactly as a person would write them. -/
abbrev RenderM := ExceptT String Unhygienic

def RenderM.run {α : Type} (x : RenderM α) : Except String α :=
  Unhygienic.run (ExceptT.run x)

partial def numTerm (lit : String) : RenderM (TSyntax `term) := do
  if lit == "Infinity" then `(floatInf)
  else if lit == "NaN" then `(floatNaN)
  else if lit.startsWith "-" then
    let inner ← numTerm (lit.drop 1).toString
    `(-$inner)
  else if lit.any (fun c => c == '.' || c == 'e') then
    pure ⟨Syntax.mkScientificLit lit⟩
  else
    pure ⟨Syntax.mkNumLit lit⟩

/-- A plain identifier. The IR's names come from TypeScript identifiers,
which are Lean-atomic; anything else is not emittable. -/
def identTerm (name : String) : RenderM Ident := do
  unless name.length > 0 && name.front.isAlpha &&
      name.all (fun c => c.isAlphanum || c == '_') do
    throw s!"'{name}' is not an emittable identifier yet"
  return mkIdent (Name.mkSimple name)

/-- A module path as one name component. It is not a Lean identifier, so
it prints between guillemets; a path containing one, or a control
character, would break the component when the artifact is re-parsed. -/
def modulePathIdent (path : String) : RenderM Name := do
  unless path.length > 0 && !("/".isPrefixOf path) &&
      path.all (fun c => c.toNat ≥ 32 && c != '«' && c != '»') do
    throw s!"'{path}' is not an emittable module path"
  return Name.mkSimple path

/-- The names the emitted text references unqualified. The artifact is
re-parsed plain text, so a binder or parameter spelled like one would
capture the reference. -/
def reservedNames : List String :=
  ["pure", "ballIco", "floatInf", "floatNaN", "Float", "Number", "Int",
   "JsM", "JsNumber", "Bool", "TsModel", "JsError", "mut", "self"]

/-- A binder or parameter: the source name, primed out of the reserved
vocabulary — a spelling no TS identifier has. -/
def scopedIdent (name : String) : RenderM Ident := do
  let _ ← identTerm name
  if reservedNames.contains name then
    return mkIdent (Name.mkSimple (name ++ "'"))
  return mkIdent (Name.mkSimple name)

/-- A model reference: emitted defs live under the old pipeline's
`TsModel` namespace, so they collide with no root-level name and no
binder can capture them. A dependency's models sit one component deeper,
under their module's entry-relative path. -/
def modelIdent (module : Option String) (name : String) : RenderM Ident := do
  let _ ← identTerm name
  match module with
  | none => return mkIdent (`TsModel ++ Name.mkSimple name)
  | some m =>
    return mkIdent (`TsModel ++ (← modulePathIdent m) ++ Name.mkSimple name)

/-- A field's source spelling as one name component; '#'-spelled privates
print between guillemets, which parse back unchanged. -/
def fieldComponent (field : String) : RenderM Name := do
  unless field.length > 0 &&
      field.all (fun c => c.toNat ≥ 32 && c != '«' && c != '»') do
    throw s!"'{field}' is not an emittable field name"
  return Name.mkSimple field

/-- A field's binder ident. The printer never escapes a name whose root
component starts with '#' — it reads those as delaborator pseudo-syntax —
and a bare `#v` does not parse back, so a non-atomic spelling carries its
guillemets inside the component. An ordinary field prints as itself. -/
def fieldIdent (field : String) : RenderM Ident := do
  let _ ← fieldComponent field
  let atomic :=
    (field.front.isAlpha || field.front == '_') &&
      field.all (fun c => c.isAlphanum || c == '_')
  return mkIdent (Name.mkSimple (if atomic then field else "«" ++ field ++ "»"))

/-- A class's structure lives beside the functions, under `TsModel`. -/
def classIdent (module : Option String) (name : String) : RenderM Ident :=
  modelIdent module name

/-- A member of a class: the constructor model, or a getter. -/
def classMember (module : Option String) (cls member : String) :
    RenderM Ident := do
  let _ ← identTerm member
  return mkIdent ((← classIdent module cls).getId ++ Name.mkSimple member)

/-- The constructor local that carries field F: «this.F», a spelling no
TypeScript identifier can take, so no source name captures it. -/
def ctorLocal (field : String) : RenderM Ident := do
  return mkIdent (← fieldComponent ("this." ++ field))

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
    | "!" => return ⟨← `((!$t)), lifted⟩
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
    -- JS evaluates the right operand only when the left leaves the answer
    -- open; a lift there renders behind the choice — the nested do is the
    -- hoist barrier — so a throw in the right arm never fires early. The
    -- ascription is load-bearing: an unascribed nested do reads its return
    -- type off the enclosing do, which is the function's, not Bool.
    | "||" =>
      if rl then
        return ⟨← `((← if $lt then pure true else ((do return $rt) : JsM Bool))), true⟩
      return ⟨← `(($lt || $rt)), ll⟩
    | "&&" =>
      if rl then
        return ⟨← `((← if $lt then ((do return $rt) : JsM Bool) else pure false)), true⟩
      return ⟨← `(($lt && $rt)), ll⟩
    | _ => throw s!"operator '{op}' is not in the emission slice yet"
  | .sameValue l r => do
    let ⟨lt, ll⟩ ← valueTerm coerced l
    let ⟨rt, rl⟩ ← valueTerm coerced r
    return ⟨← `(Number.FloatOps.sameValue $lt $rt), ll || rl⟩
  | .mathSqrt a => do
    let ⟨t, lifted⟩ ← valueTerm coerced a
    return ⟨← `(Float.sqrt $t), lifted⟩
  | .mathAbs a => do
    let ⟨t, lifted⟩ ← valueTerm coerced a
    return ⟨← `(Float.abs $t), lifted⟩
  | .numberIsFinite a => do
    let ⟨t, lifted⟩ ← valueTerm coerced a
    return ⟨← `(Float.isFinite $t), lifted⟩
  | .numberIsNaN a => do
    let ⟨t, lifted⟩ ← valueTerm coerced a
    return ⟨← `(Float.isNaN $t), lifted⟩
  | .call callee module args => do
    let c ← callTerm coerced callee module args
    return ⟨← `((← $c:term)), true⟩
  | .newObj cls module args => do
    let c ← classMember module cls "construct"
    let argTerms ← args.mapM (fun a => return (← valueTerm coerced a).term)
    let call ← if argTerms.isEmpty then pure (c : TSyntax `term) else `($c $argTerms*)
    return ⟨← `((← $call:term)), true⟩
  | .getterRead cls module name obj => do
    let g ← classMember module cls name
    let ⟨o, _⟩ ← valueTerm coerced obj
    return ⟨← `((← $g:term $o:term)), true⟩
  -- A field projection is pure; an object that lifts keeps its lift, so
  -- the `(← ...)` nests and JS evaluation order survives.
  | .fieldRead cls module field obj => do
    let p := mkIdent ((← classIdent module cls).getId ++ (← fieldComponent field))
    let ⟨o, lifted⟩ ← valueTerm coerced obj
    return ⟨← `($p:term $o:term), lifted⟩
  -- The receiver renders ahead of the arguments, so its lift elaborates
  -- first: JS evaluates a call's receiver before its arguments.
  | .methodCall cls module name obj args => do
    let m ← classMember module cls name
    let ⟨o, _⟩ ← valueTerm coerced obj
    let argTerms ← args.mapM (fun a => return (← valueTerm coerced a).term)
    return ⟨← `((← $m:term $o:term $argTerms*)), true⟩
  | .selfRef => return ⟨mkIdent (Name.mkSimple "self"), false⟩

/-- A call as the `JsM` value it denotes, its arguments still
value-level. -/
partial def callTerm (coerced : String → Bool) (callee : String)
    (module : Option String) (args : Array JsExpr) : RenderM (TSyntax `term) := do
  let f ← modelIdent module callee
  let argTerms ← args.mapM (fun a => return (← valueTerm coerced a).term)
  if argTerms.isEmpty then pure f else `($f $argTerms*)

end

/-- A `JsM`-valued rendering of an expression, for the sides of an
equation: a bare call stays the call (and pins the monad for the other
side), anything else lifts with `pure` or a `do return`. The flag says
whether the term pins `JsM` on its own. -/
def monadicTerm (coerced : String → Bool) :
    JsExpr → RenderM (TSyntax `term × Bool)
  | .call callee module args => do
    let liftedArgs ← args.anyM fun a =>
      return (← valueTerm coerced a).lifted
    if liftedArgs then
      let ⟨t, _⟩ ← valueTerm coerced (.call callee module args)
      return (← `(do return $t), false)
    return (← callTerm coerced callee module args, true)
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
partial def stmtsDoSeq (straight : Option (List String)) (stmts : Array JsStmt) :
    RenderM (TSyntax ``Lean.Parser.Term.doSeqIndent) := do
  let elems ←
    if stmts.isEmpty then pure #[← `(doElem| pure ())]
    else stmts.mapM (stmtDoElem straight)
  `(Lean.Parser.Term.doSeqIndent| $[$elems:doElem]*)

/-- One statement. `straight` is set only inside a constructor body,
where it names the fields whose single assignment sits at the top level:
those render as plain `let`s, the rest as reassignments of a prelude. -/
partial def stmtDoElem (straight : Option (List String)) :
    JsStmt → RenderM (TSyntax `doElem)
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
  | .ite c thn els => iteElem straight c thn els
  | .fieldSet f e => do
    let some fields := straight
      | throw "a field assignment outside a constructor is not renderable"
    let x ← ctorLocal f
    if fields.contains f then
      `(doElem| let $x:ident : JsNumber := $(← bodyTerm e))
    else
      `(doElem| $x:ident := $(← bodyTerm e))

/-- An `if` statement. An else arm that is itself exactly one `if` joins
the chain as `else if`, the way the source spells it: the nested doIf's
condition and arms are grafted onto the outer node's else-if groups,
which is syntax the quotations built — only rearranged. -/
partial def iteElem (straight : Option (List String)) (c : JsExpr)
    (thn : Array JsStmt) (els : Option (Array JsStmt)) :
    RenderM (TSyntax `doElem) := do
  let ct ← bodyTerm c
  let thenSeq ← stmtsDoSeq straight thn
  match els with
  | none => `(doElem| if $ct then $thenSeq:doSeqIndent)
  | some #[.ite c2 t2 e2] => do
    let inner ← iteElem straight c2 t2 e2
    let base ← `(doElem| if $ct then $thenSeq:doSeqIndent)
    -- doIf's shape: "if", cond, "then", seq, else-if groups, else?.
    let a := inner.raw.getArgs
    let elseIf := mkNode `group
      #[mkNode `group #[mkAtom "else", mkAtom "if"], a[1]!, a[2]!, a[3]!]
    return ⟨(base.raw.setArg 4 (mkNullNode (#[elseIf] ++ a[4]!.getArgs))).setArg 5 a[5]!⟩
  | some elseStmts => do
    let elseSeq ← stmtsDoSeq straight elseStmts
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
  let name ← modelIdent f.module f.name
  let params ← f.params.mapM scopedIdent
  let assigned := f.body.toList.flatMap assignedNames
  let rebound ← f.params.filterMapM fun p => do
    unless assigned.contains p do return none
    let pi ← scopedIdent p
    return some (← `(doElem| let mut $pi:ident := $pi))
  let body ← f.body.mapM (stmtDoElem none)
  let elems := rebound ++ body
  -- Dual-tagged like the old models: the js_norm closers and the grind
  -- rung both unfold a model by its equations.
  `(@[js_norm, grind] def $name ($params* : JsNumber) : JsM JsNumber := do
      $[$elems:doElem]*)

/-- Whether a statement tree assigns F anywhere. -/
partial def hasSetOf (f : String) : JsStmt → Bool
  | .fieldSet g _ => g == f
  | .ite _ thn els => (thn ++ els.getD #[]).any (hasSetOf f)
  | _ => false

/-- Whether F's single assignment sits at the constructor's top level and
nowhere else, so it can render as a plain let in place of a mut prelude. -/
def straightSet (body : Array JsStmt) (f : String) : Bool :=
  body.any (fun s => match s with | .fieldSet g _ => g == f | _ => false) &&
  body.all (fun s => match s with
    | .ite _ thn els => !(thn ++ els.getD #[]).any (hasSetOf f)
    | _ => true)

def structCommand (c : EmitClass) : RenderM (TSyntax `command) := do
  let cls ← classIdent c.module c.name
  let fields ← c.fields.mapM fieldIdent
  if fields.isEmpty then `(structure $cls)
  else `(structure $cls where $[$fields:ident : JsNumber]*)

/-- The constructor as a `JsM`-returning function over the structure. A
field the body assigns inside a branch needs a mut prelude; the dummy `0`
is never read, since every falling-through path assigns before the end. -/
def ctorCommand (c : EmitClass) : RenderM (TSyntax `command) := do
  let name ← classMember c.module c.name "construct"
  let cls ← classIdent c.module c.name
  let params ← c.ctorParams.mapM scopedIdent
  let straight := c.fields.toList.filter (straightSet c.ctorBody)
  let assigned := c.ctorBody.toList.flatMap assignedNames
  let rebound ← c.ctorParams.filterMapM fun p => do
    unless assigned.contains p do return none
    let pi ← scopedIdent p
    return some (← `(doElem| let mut $pi:ident := $pi))
  let prelude ← (c.fields.filter (fun f => !straight.contains f)).mapM fun f => do
    `(doElem| let mut $(← ctorLocal f):ident : JsNumber := 0)
  let body ← c.ctorBody.mapM (stmtDoElem (some straight))
  let mk := mkIdent (cls.getId ++ `mk)
  let mkArgs ← c.fields.mapM ctorLocal
  let ret ←
    if mkArgs.isEmpty then `(doElem| return $mk)
    else `(doElem| return $mk $mkArgs*)
  let elems := rebound ++ prelude ++ body ++ #[ret]
  if params.isEmpty then
    `(@[js_norm, grind] def $name : JsM $cls := do
        $[$elems:doElem]*)
  else
    `(@[js_norm, grind] def $name ($params* : JsNumber) : JsM $cls := do
        $[$elems:doElem]*)

/-- A method as a function of the instance and its parameters; the
receiver is `self`, in the reserved vocabulary, so no source name
captures it. An assigned parameter is rebound `let mut`, like a free
function's. -/
def methodCommand (c : EmitClass) (m : EmitMethod) : RenderM (TSyntax `command) := do
  let name ← classMember c.module c.name m.name
  let cls ← classIdent c.module c.name
  let self := mkIdent (Name.mkSimple "self")
  let params ← m.params.mapM scopedIdent
  let assigned := m.body.toList.flatMap assignedNames
  let rebound ← m.params.filterMapM fun p => do
    unless assigned.contains p do return none
    let pi ← scopedIdent p
    return some (← `(doElem| let mut $pi:ident := $pi))
  let body ← m.body.mapM (stmtDoElem none)
  let elems := rebound ++ body
  if params.isEmpty then
    `(@[js_norm, grind] def $name ($self : $cls) : JsM JsNumber := do
        $[$elems:doElem]*)
  else
    `(@[js_norm, grind] def $name ($self : $cls) ($params* : JsNumber) : JsM JsNumber := do
        $[$elems:doElem]*)

/-- A getter is the zero-parameter method shape. -/
def getterCommand (c : EmitClass) (g : EmitGetter) : RenderM (TSyntax `command) :=
  methodCommand c { name := g.name, params := #[], body := g.body }

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
  -- A dependency's declarations are contiguous and introduced by their
  -- module, the way the old pipeline writes it; the entry's carry none.
  let mut fromModule : Option String := none
  for d in e.declarations do
    let module := match d with | .fn f => f.module | .cls c => c.module
    if module != fromModule then
      fromModule := module
      if let some m := module then
        blocks := blocks.push s!"-- module {m}"
    match d with
    | .fn f =>
      let cmd ← rendered (fnCommand f)
      blocks := blocks.push
        (commentLines f.source ++ "\n" ++ prettyLines (← ppCommand cmd))
    | .cls c =>
      -- The source echo introduces the structure; the constructor and
      -- each getter follow as their own blocks.
      let st ← rendered (structCommand c)
      blocks := blocks.push
        (commentLines c.source ++ "\n" ++ prettyLines (← ppCommand st))
      blocks := blocks.push (prettyLines (← ppCommand (← rendered (ctorCommand c))))
      for g in c.getters do
        blocks := blocks.push
          (prettyLines (← ppCommand (← rendered (getterCommand c g))))
      for m in c.methods do
        blocks := blocks.push
          (prettyLines (← ppCommand (← rendered (methodCommand c m))))
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
