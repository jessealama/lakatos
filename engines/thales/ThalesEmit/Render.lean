import Lean
import ThalesDsl
import ThalesEmit.Json

/-! IR → `TSyntax` → text. Every line of Lean code in the artifact is
built by quotation and printed by Lean's pretty-printer; the only strings
assembled by hand are comments and the fixed header. Shapes beyond this
slice — multi-statement bodies, module-qualified names — are refused
with a message naming the gap, never approximated. -/

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
   "JsM", "JsNumber", "Bool", "TsModel"]

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

def fnCommand (f : EmitFn) : RenderM (TSyntax `command) := do
  let name ← modelIdent f.name
  let params ← f.params.mapM scopedIdent
  match f.body with
  | #[.ret e] =>
    let ⟨body, _⟩ ← valueTerm (fun _ => false) e
    -- Dual-tagged like the old models: the js_norm closers and the grind
    -- rung both unfold a model by its equations.
    `(@[js_norm, grind] def $name ($params* : JsNumber) : JsM JsNumber := do
        return $body)
  | _ => throw s!"'{f.name}': only single-return bodies are in the emission slice yet"

def obligationCommand (e : Emission) (o : Obligation) : RenderM (TSyntax `command) := do
  let file := Syntax.mkStrLit e.file
  let fn := Syntax.mkStrLit o.function
  let prop := Syntax.mkStrLit o.property
  match o.payload with
  | .bare => `(#thales_prove $file $fn $prop)
  | .structured binders conclusion =>
    let bound := binders.map (·.name)
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
      | .istrue expr => do
        let ⟨t, lifted⟩ ← valueTerm coerced expr
        -- A boolean island must evaluate to `pure true`, the same shape
        -- the old pipeline elaborates.
        if lifted then `(((do return $t) : JsM Bool) = pure true)
        else `((pure $t : JsM Bool) = pure true)
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

/-- The full artifact text. Pretty-printing runs in `CoreM` against an
environment that imports `ThalesDsl`, which carries every syntax the
quotations build. -/
def renderEmission (e : Emission) : CoreM String := do
  let mut blocks : Array String := #[header e]
  for f in e.declarations do
    let cmd ← rendered (fnCommand f)
    blocks := blocks.push
      (commentLines f.source ++ "\n" ++ (← ppCommand cmd).pretty 100)
  for o in e.obligations do
    let cmd ← rendered (obligationCommand e o)
    blocks := blocks.push
      (s!"-- @ensures\{{o.property}} {o.formula}\n" ++ (← ppCommand cmd).pretty 100)
  return String.intercalate "\n\n" blocks.toList ++ "\n"
where
  rendered (x : RenderM (TSyntax `command)) : CoreM (TSyntax `command) := do
    match RenderM.run x with
    | .error msg => throwError msg
    | .ok cmd => pure cmd
  ppCommand (cmd : TSyntax `command) : CoreM Format :=
    PrettyPrinter.ppCommand ⟨unscope cmd.raw⟩

end ThalesEmit
