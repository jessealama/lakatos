import ThalesEmit.Render
import ThalesEmit.Ast

/-! Which declarations carry a correspondence obligation, and what it says.

`#thales_validate` (`ThalesDsl/Validate.lean`) is the command; this is the
emitter's side of it. Every entry-module function and constant gets a
command — the obligation when the declaration is one this slice can state
it for, and otherwise the bare form carrying the reason it is not. One
channel, one line per declaration, so the CLI has one thing to join.

The reasons are the design record's D7 (the residual's construct, the
decoder's refused construct, and — from the command itself — the stuck
and budget reasons), plus the two this slice needs: a closure the
frontend could not close, and a parameter this slice does not quantify.

**A dependency's declaration gets nothing.** Its own artifact validates it
when its file is proved, and this artifact's obligation runs the whole
closure — the dependency included — against the entry's model, so nothing
about this file's annotations is lost. It also keeps the model line's
`function` field the plain name a verdict's identity carries. -/

namespace ThalesEmit

open Lean

/-- What a declaration's `#thales_validate` command says. `none` is no
command at all, which is what a dependency's declaration gets. -/
inductive ValidatePlan where
  /-- The correspondence obligation, as a term. -/
  | obligation (t : Term)
  /-- No obligation, and why. -/
  | bare (reason : String)
  | none

/-- The refusal texts of an owner's own residual sites, in declaration
order — the same strings an `Inappropriate` verdict lists. -/
def residualConstructs (e : Emission) (module : Option String) (owner : String) :
    List String :=
  e.declarations.toList.filterMap fun d => match d with
    | .residual r => if r.module == module && r.owner == owner then some r.construct else none
    | _ => none

/-- Every sub-expression of an expression, itself included. -/
partial def subExprs (x : JsExpr) : List JsExpr :=
  x :: (match x with
    | .unop _ a | .project _ a | .optionTest a _ | .optionGet a | .typeofTest a _ =>
      subExprs a
    | .binop _ a b | .sameValue a b | .jsvalEq _ a b => subExprs a ++ subExprs b
    | .cond c t f => subExprs c ++ subExprs t ++ subExprs f
    | .builtin _ _ args | .call _ _ args | .newObj _ _ args | .residual _ _ _ args =>
      args.toList.flatMap subExprs
    | .getterRead _ _ _ o | .fieldRead _ _ _ o => subExprs o
    | .methodCall _ _ _ o args => subExprs o ++ args.toList.flatMap subExprs
    | .optionInject o => (o.map subExprs).getD []
    | .inject _ o => (o.map subExprs).getD []
    | .num _ | .bool _ | .id _ | .builtinRead _ _ | .selfRef | .constRead _ _ => [])

/-- Every expression a statement tree holds, sub-expressions included. -/
partial def stmtExprs (s : JsStmt) : List JsExpr :=
  match s with
  | .ret x | .discard x | .constDecl _ _ x | .letDecl _ _ x | .assign _ x
  | .fieldSet _ x => subExprs x
  | .throwErr _ => []
  | .ite c thn els =>
    subExprs c ++ thn.toList.flatMap stmtExprs ++ (els.getD #[]).toList.flatMap stmtExprs

/-- The callables a body reaches directly, as the `(module, owner)` pairs
a residual site is keyed by. A class member's owner is `C#member`, a
construction's is `C#constructor` — the spellings `EmitResidual.owner`
uses. -/
def reachedOwners (body : Array JsStmt) : List (Option String × String) :=
  body.toList.flatMap stmtExprs |>.filterMap fun x => match x with
    | .call callee m _ => some (m, callee)
    | .newObj c m _ => some (m, c ++ "#constructor")
    | .getterRead c m n _ => some (m, c ++ "#" ++ n)
    | .methodCall c m n _ _ => some (m, c ++ "#" ++ n)
    | _ => none

/-- The body an owner names, so the walk can follow a call into it. -/
def bodyOf (e : Emission) (module : Option String) (owner : String) :
    Option (Array JsStmt) :=
  match owner.splitOn "#" with
  | [f] =>
    e.declarations.findSome? fun d => match d with
      | .fn g => if g.module == module && g.name == f then some g.body else none
      | _ => none
  | [c, member] =>
    e.declarations.findSome? fun d => match d with
      | .cls k =>
        if k.module != module || k.name != c then none
        else if member == "constructor" then some k.ctorBody
        else match k.getters.find? (·.name == member) with
          | some g => some g.body
          | none => (k.methods.find? (·.name == member)).map (·.body)
      | _ => none
  | _ => none

/-- The constructs a tainted declaration is tainted by: its own sites
first, and failing those the sites of every tainted callee it reaches,
transitively. A function tainted through a callee carries no residual of
its own — the site belongs to the callee — so the walk is what makes the
reason name a construct rather than a shrug. -/
partial def taintConstructs (e : Emission) (fuel : Nat)
    (visited : List (Option String × String)) (module : Option String) (owner : String) :
    List String :=
  if fuel == 0 || visited.contains (module, owner) then []
  else
    let visited := (module, owner) :: visited
    let own := residualConstructs e module owner
    match bodyOf e module owner with
    | none => own
    | some body =>
      own ++ (reachedOwners body).flatMap fun (m, o) =>
        taintConstructs e (fuel - 1) visited m o

/-- Why a tainted function has no obligation: the constructs, joined the
way an `Inappropriate` verdict joins its sites. A taint whose site the
walk cannot reach still says something true. -/
def taintReason (e : Emission) (f : EmitFn) : String :=
  let own := residualConstructs e f.module f.name
  let cs := if own.isEmpty then
      (reachedOwners f.body).flatMap fun (m, o) =>
        taintConstructs e (e.declarations.size + 1) [(f.module, f.name)] m o
    else own
  if cs.isEmpty then s!"'{f.name}' reaches code outside the model"
  else "; ".intercalate cs.eraseDups

/-- The reader that recognizes a declaration's return value as its model's
type. -/
def readerTerm : ReturnTy → RenderM Term
  | .number => `(Tarski.readNumber)
  | .bool => `(Tarski.readBool)

/-- The obligation of a free function: the evaluator's run of the
declaration's own closure, followed by a call with the quantified
arguments spliced in as literals, projected — equal to the model applied
to the same arguments, injected. The AST spelling is `Ast.lean`'s, so the
call statement is written exactly as the closure above it is. -/
def fnObligation (f : EmitFn) : RenderM Term := do
  let model ← modelIdent f.module f.name
  let ast := astIdent model
  let reader ← readerTerm f.returns
  let xs ← f.params.mapM fun p => scopedIdent p.name
  let args ← (f.params.zip xs).mapM fun (p, x) =>
    match p.ty with
    | .number => ctorApp "numLit" #[x]
    | .bool => ctorApp "boolLit" #[x]
    | _ => throw s!"parameter '{p.name}' of '{f.name}' has no AST literal"
  -- The JS spelling, never the primed binder: the call names the function
  -- the closure declares.
  let callee ← ctorApp "ident" #[strTerm f.name]
  let call ← ctorApp "call" #[callee, ← `([$args,*])]
  let stmt ← ctorApp "exprStmt" #[call]
  let body ←
    `(Tarski.project $reader (Tarski.runScript ($ast ++ [$stmt]))
        = some (Tarski.Outcome.ofModel ($model $xs*)))
  let binders ← paramBinders f.params
  if binders.isEmpty then pure body else `(∀ $binders*, $body)

/-- The obligation of a module constant: the closure, then a read of the
name. A constant's model is a `JsNumber` and not a `JsM`, so the
comparison is against `Outcome.value` rather than against
`Outcome.ofModel`. -/
def constObligation (c : EmitConstant) : RenderM Term := do
  let model ← modelIdent c.module c.name
  let ast := astIdent model
  let stmt ← ctorApp "exprStmt" #[← ctorApp "ident" #[strTerm c.name]]
  `(Tarski.project Tarski.readNumber (Tarski.runScript ($ast ++ [$stmt]))
      = some (Tarski.Outcome.value $model))

/-- A declaration's closure as the plan reads it: present and decoded, or
the reason it is not. -/
def astReason (name : String) : Option DeclAst → Option String
  | none => some s!"the closure of '{name}' is not a closed script"
  | some (.unsupported k) => some s!"unsupported: {k}"
  | some (.program _) => none

/-- What a free function gets. A dependency's declaration gets nothing; a
tainted one, a closure-less one, and one the decoder refused each get the
bare form; a parameter outside `number` and `boolean` gets it too — a
`JsVal` needs a literal map and a tag split the closer does not have
yet, and a class parameter is #482's. -/
def fnPlan (e : Emission) (f : EmitFn) : RenderM ValidatePlan := do
  if f.module.isSome then return .none
  if f.tainted then return .bare (taintReason e f)
  if let some r := astReason f.name f.ast then return .bare r
  match f.params.find? fun p => p.ty != .number && p.ty != .bool with
  | some p => return .bare s!"parameter '{p.name}' of '{f.name}' is not a number or boolean"
  | none => return .obligation (← fnObligation f)

/-- What a module constant gets. A constant is never tainted — the
frontend's initializer slice has no residual — so only its closure can
stand in the way. -/
def constPlan (c : EmitConstant) : RenderM ValidatePlan := do
  if c.module.isSome then return .none
  if let some r := astReason c.name c.ast then return .bare r
  return .obligation (← constObligation c)

/-- The command a plan renders as. -/
def validateCommand (file : String) (fn : String) :
    ValidatePlan → RenderM (Option (TSyntax `command))
  | .none => pure none
  | .obligation t => do
    let f := Syntax.mkStrLit file
    let n := Syntax.mkStrLit fn
    return some (← `(#thales_validate $f $n := $t:term))
  | .bare reason => do
    let f := Syntax.mkStrLit file
    let n := Syntax.mkStrLit fn
    let r := Syntax.mkStrLit reason
    return some (← `(#thales_validate $f $n unvalidated $r))

end ThalesEmit
