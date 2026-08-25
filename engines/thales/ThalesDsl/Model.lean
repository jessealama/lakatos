import Lean
import Js.Number.FloatOps
import Js.Runtime
import ThalesDsl.Binders
import ThalesDsl.Norm
import ThalesDsl.Syntax

namespace ThalesDsl

open Lean Elab Command
open Js

/-- A registered TS function model. This slice types every parameter and
result as `Float`, so arity is the whole signature. -/
structure ModelInfo where
  tsName : String
  declName : Name
  arity : Nat
deriving Inhabited

initialize modelExt : SimplePersistentEnvExtension ModelInfo (List ModelInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => e :: s
    addImportedFn := fun arrs => arrs.flatten.toList
  }

def findModel? (env : Environment) (tsName : String) : Option ModelInfo :=
  (modelExt.getState env).find? (·.tsName == tsName)

/-- A declaration whose `ts_def` failed to elaborate. `construct` names the
TypeScript the model does not cover — an opaque node's kind, or an operator
with no model — and is what separates a statement about the input from an
engine malfunction; `none` means some other elaboration failure. -/
structure FailedDecl where
  tsName : String
  construct : Option String
  reason : String
deriving Inhabited

initialize failedExt : SimplePersistentEnvExtension FailedDecl (List FailedDecl) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => e :: s
    addImportedFn := fun arrs => arrs.flatten.toList
  }

def findFailed? (env : Environment) (tsName : String) : Option FailedDecl :=
  (failedExt.getState env).find? (·.tsName == tsName)

/-- The construct name and `.ts` source position of an opaque node. -/
def opaqueInfo? (stx : Syntax) : Option (String × String) :=
  match stx with
  | `(ts_expr| ts.opaque[$kind:str]($line:num, $col:num)) =>
    some (kind.getString, s!"{line.getNat}:{col.getNat}")
  | `(ts_stmt| ts.opaque[$kind:str]($line:num, $col:num)) =>
    some (kind.getString, s!"{line.getNat}:{col.getNat}")
  | _ => none

/-- The first opaque node in `stx`, in tree order. -/
partial def findOpaque? (stx : Syntax) : Option (String × String) :=
  opaqueInfo? stx <|> stx.getArgs.findSome? findOpaque?

def unmappedMsg (construct pos : String) : String :=
  s!"unmapped TypeScript construct '{construct}' at {pos}"

/-- Operators deliberately left without a model, and why. These are refusals
on the merits, not gaps in the slice: a model would have to pick semantics
the language does not fix. -/
def unmodeledOperator? : String → Option String
  | "**" => some <|
      "'**' is implementation-approximated in JavaScript, so any model would "
      ++ "certify results a conforming engine may disagree with"
  | _ => none

/-- The operator and reason of the first refused operator in `stx`, in tree
order. Scanned ahead of elaboration so the refusal reads as a statement about
the input, the way an opaque node does, rather than as a failed elaboration. -/
partial def findUnmodeledOp? (stx : Syntax) : Option (String × String) :=
  (match stx with
    | `(ts_expr| ts.binop[$op:str]($_lhs:ts_expr, $_rhs:ts_expr)) =>
      (unmodeledOperator? op.getString).map (op.getString, ·)
    | _ => none) <|> stx.getArgs.findSome? findUnmodeledOp?

/-- Every function name `stx` calls, in tree order. -/
partial def callNames (stx : Syntax) : List String :=
  let here := match stx with
    | `(ts_expr| ts.call[$f:str]($_args:ts_expr,*)) => [f.getString]
    | _ => []
  here ++ stx.getArgs.toList.flatMap callNames

/-- The construct and reason of the first callee in `names` whose own
`ts_def` failed on a named construct: the refusal travels with the call, so
a caller is outside the model exactly when what it calls is. A callee that
failed for any other reason is the engine's problem, not the input's, and
is left to elaboration to report. -/
def calleeFailure? (env : Environment) (names : List String) : Option (String × String) :=
  names.findSome? fun n =>
    if (findModel? env n).isSome then none
    else do
      let failed ← findFailed? env n
      let construct ← failed.construct
      some (construct, s!"'{n}' could not be modeled: {failed.reason}")

/-- Why `p` cannot be attempted under the containment contract: an opaque
node or a refused operator in the formula itself, or a call to a declaration
whose `ts_def` failed on one. `none` means the formula may elaborate. -/
def propInappropriate? (env : Environment) (p : TSyntax `ts_prop) : Option String :=
  (findOpaque? p.raw).map (fun (construct, pos) => unmappedMsg construct pos)
  <|> (findUnmodeledOp? p.raw).map Prod.snd
  <|> (calleeFailure? env (callNames p.raw)).map Prod.snd

/-- The value types of the slice. Expression elaboration is type-directed:
the operator decides its operand and result types. `num` is binary64 — the
type a TypeScript `number` parameter actually holds. -/
inductive ValTy where
  | num
  | bool
deriving BEq, Repr

def ValTy.describe : ValTy → String
  | .num => "a number"
  | .bool => "a boolean"

/-- Interval endpoints stay exact integers: they index the enumeration,
they are not values the modelled program computes with. -/
def tsIntLitToInt : TSyntax ``tsIntLit → CommandElabM (TSyntax `term)
  | `(tsIntLit| $n:num) => `(($n : Int))
  | `(tsIntLit| -$n:num) => `((-$n : Int))
  | stx => throwErrorAt stx "malformed integer literal"

/-- A decimal literal, transcribed verbatim. Lean rounds it exactly as
JavaScript does, so no adjustment is needed here. -/
def tsFloatLitToTerm : TSyntax ``tsFloatLit → CommandElabM (TSyntax `term)
  | `(tsFloatLit| $n:scientific) => `(($n : Float))
  | `(tsFloatLit| -$n:scientific) => `((-$n : Float))
  | `(tsFloatLit| $n:num) => `(($n : Float))
  | `(tsFloatLit| -$n:num) => `((-$n : Float))
  | `(tsFloatLit| Infinity) => `(floatInf)
  | `(tsFloatLit| -Infinity) => `((-floatInf))
  | stx => throwErrorAt stx "malformed float literal"

/-- `ts#argN`: cannot capture, since `#` never occurs in a TS identifier. -/
def freshArg (i : Nat) : Ident := mkIdent (Name.mkSimple s!"ts#arg{i}")

/-- Transcribes a `ts_expr` into a Lean term of type `JsM Float` /
`JsM Bool` per `expected`. Registry misses and operator/type mismatches
throw here, so `#thales_prove` can contain them per command. -/
partial def evalExpr (vars : List String) (expected : ValTy) :
    TSyntax `ts_expr → CommandElabM (TSyntax `term)
  | `(ts_expr| ts.num[$n:tsFloatLit]) => do
    unless expected == .num do
      throwErrorAt n "a numeric literal cannot be {expected.describe}"
    `((pure $(← tsFloatLitToTerm n) : JsM Float))
  | `(ts_expr| ts.id[$x:str]) => do
    unless vars.contains x.getString do
      throwErrorAt x "unbound identifier '{x.getString}'"
    unless expected == .num do
      throwErrorAt x "identifier '{x.getString}' is a number, not {expected.describe}"
    `((pure $(mkIdent (Name.mkSimple x.getString)) : JsM Float))
  | `(ts_expr| ts.binop[$op:str]($l:ts_expr, $r:ts_expr)) => do
    let lt ← evalExpr vars .num l
    let rt ← evalExpr vars .num r
    -- The combining lambda is interpolated into the same quotation that
    -- binds the operands, keeping hygiene consistent.
    let arith (f : TSyntax `term) : CommandElabM (TSyntax `term) := do
      unless expected == .num do
        throwErrorAt op "operator '{op.getString}' yields a number, not {expected.describe}"
      `((($lt >>= fun a => $rt >>= fun b => pure ($f a b)) : JsM Float))
    -- The comparisons are IEEE predicates, already Bool-valued, so there is
    -- no Prop to `decide` here.
    let cmp (f : TSyntax `term) : CommandElabM (TSyntax `term) := do
      unless expected == .bool do
        throwErrorAt op "operator '{op.getString}' yields a boolean, not {expected.describe}"
      `((($lt >>= fun a => $rt >>= fun b => pure ($f a b)) : JsM Bool))
    match op.getString with
    | "+" => arith (← `(fun x y => x + y))
    | "-" => arith (← `(fun x y => x - y))
    | "*" => arith (← `(fun x y => x * y))
    | "/" => arith (← `(fun x y => x / y))
    | "%" => arith (← `(fun x y => Js.Number.FloatOps.tsRem x y))
    | "<" => cmp (← `(fun x y => Float.lt x y))
    | "<=" => cmp (← `(fun x y => Float.le x y))
    | ">" => cmp (← `(fun x y => Float.lt y x))
    | ">=" => cmp (← `(fun x y => Float.le y x))
    | "===" => cmp (← `(fun x y => Float.beq x y))
    | "!==" => cmp (← `(fun x y => !Float.beq x y))
    | other =>
      -- Reachable only for a refused operator the pre-scans missed; the
      -- reason must still be the one they would have recorded.
      match unmodeledOperator? other with
      | some reason => throwErrorAt op reason
      | none => throwErrorAt op "operator '{other}' has no model in this slice"
  | `(ts_expr| ts.unop[$op:str]($x:ts_expr)) => do
    let xt ← evalExpr vars .num x
    unless expected == .num do
      throwErrorAt op "operator '{op.getString}' yields a number, not {expected.describe}"
    match op.getString with
    | "-" => `((($xt >>= fun a => pure (-a)) : JsM Float))
    | "+" =>
      -- ToNumber on a value already a number: the identity.
      pure xt
    | other =>
      match unmodeledOperator? other with
      | some reason => throwErrorAt op reason
      | none => throwErrorAt op "operator '{other}' has no model in this slice"
  | `(ts_expr| ts.opaque[$kind:str]($line:num, $col:num)) =>
    throwErrorAt kind (unmappedMsg kind.getString s!"{line.getNat}:{col.getNat}")
  | `(ts_expr| ts.call[$f:str]($args:ts_expr,*)) => do
    let some info := findModel? (← getEnv) f.getString
      | match findFailed? (← getEnv) f.getString with
        | some failed => throwErrorAt f "'{f.getString}' has no model: {failed.reason}"
        | none => throwErrorAt f "no model registered for '{f.getString}'"
    unless info.arity == args.getElems.size do
      throwErrorAt f
        "'{f.getString}' expects {info.arity} argument(s), got {args.getElems.size}"
    unless expected == .num do
      throwErrorAt f "a call to '{f.getString}' yields a number, not {expected.describe}"
    let argTerms ← args.getElems.mapM (evalExpr vars .num)
    let argNames := (List.range argTerms.size).map freshArg
    let mut call : TSyntax `term ← `($(mkIdent info.declName))
    for n in argNames do
      call ← `($call $n)
    let mut body ← `(($call : JsM Float))
    for (name, arg) in (argNames.zip argTerms.toList).reverse do
      body ← `((($arg >>= fun $name => $body) : JsM Float))
    pure body
  | stx => throwErrorAt stx "unsupported expression shape"

/-! Statement lowering: a function body is a statement tree, and the model
is one `JsM Float` expression. Every statement list lowers to that same
type, so a branch whose arms disagree about returning still composes. -/

mutual

/-- Whether every path through a statement leaves the function — a return
or a throw, or an `if` whose two arms both do. Anything else falls
through, and the lowering must hand it the rest of the body. -/
partial def stmtLeaves : TSyntax `ts_stmt → Bool
  | `(ts_stmt| ts.return($_e:ts_expr)) => true
  | `(ts_stmt| ts.throw[$_k:str]) => true
  | `(ts_stmt| ts.if($_c:ts_expr) {$a:ts_stmt*} $[else {$b:ts_stmt*}]?) =>
    match b with
    | some b => stmtsLeave a && stmtsLeave b
    | none => false
  | _ => false

partial def stmtsLeave (stmts : TSyntaxArray `ts_stmt) : Bool :=
  stmts.any stmtLeaves

end

/-- The mutable names a statement list assigns, in first-assignment order.
Restricted to `muts` — an arm's own locals die with the arm, so they are
never part of the join. -/
partial def assignedIn (muts : List String) (stmts : TSyntaxArray `ts_stmt) :
    List String :=
  (stmts.toList.flatMap go).eraseDups
where
  go (s : TSyntax `ts_stmt) : List String :=
    match s with
    | `(ts_stmt| ts.assign[$x:str]($_e:ts_expr)) =>
      if muts.contains x.getString then [x.getString] else []
    | `(ts_stmt| ts.if($_c:ts_expr) {$a:ts_stmt*} $[else {$b:ts_stmt*}]?) =>
      a.toList.flatMap go ++ (b.getD #[]).toList.flatMap go
    | _ => []

/-- Names in scope, and which of them a `ts.assign` may rebind. Rebinding
is by shadowing: a reassignment binds the name again over the rest of the
list, so nothing in the elaborated term is mutable. -/
structure Scope where
  vars : List String
  muts : List String

/-- The rest of the body, as an action that builds it where it is spliced.
Identifiers inside resolve to whatever binding is innermost at that point,
which is exactly how a branch's reassignments reach the tail. Each
continuation is run at most once, so no tail is ever duplicated. -/
abbrev Cont := CommandElabM (TSyntax `term)

/-- Lowers a statement list into one `JsM Float` term, splicing `k` where
control falls off the end of the list. -/
partial def lowerStmts (fresh : IO.Ref Nat) (sc : Scope) :
    List (TSyntax `ts_stmt) → Cont → CommandElabM (TSyntax `term)
  | [], k => k
  | s :: rest, k => do
    -- A binding whose scope is the rest of the list; a bind rather than a
    -- substitution, so an unused initializer still evaluates.
    let bindLocal (mutable : Bool) (x : StrLit) (init : TSyntax `ts_expr) := do
      if sc.vars.contains x.getString then
        throwErrorAt x "'{x.getString}' shadows a binding already in scope"
      let initTerm ← evalExpr sc.vars .num init
      let sc' := { vars := sc.vars ++ [x.getString],
                   muts := if mutable then sc.muts ++ [x.getString] else sc.muts }
      let body ← lowerStmts fresh sc' rest k
      `(((($initTerm) >>= fun $(mkIdent (Name.mkSimple x.getString)) => $body) : JsM Float))
    match s with
    -- A return or a throw ends this path; whatever follows is unreachable.
    | `(ts_stmt| ts.return($e:ts_expr)) => evalExpr sc.vars .num e
    | `(ts_stmt| ts.throw[$kind:str]) =>
      `((JsM.throw (.error $kind) : JsM Float))
    | `(ts_stmt| ts.const[$x:str]($init:ts_expr)) => bindLocal false x init
    | `(ts_stmt| ts.let[$x:str]($init:ts_expr)) => bindLocal true x init
    | `(ts_stmt| ts.assign[$x:str]($e:ts_expr)) => do
      unless sc.muts.contains x.getString do
        throwErrorAt x "'{x.getString}' is not a mutable binding"
      let valTerm ← evalExpr sc.vars .num e
      let body ← lowerStmts fresh sc rest k
      `(((($valTerm) >>= fun $(mkIdent (Name.mkSimple x.getString)) => $body) : JsM Float))
    | `(ts_stmt| ts.if($c:ts_expr) {$a:ts_stmt*} $[else {$b:ts_stmt*}]?) => do
      let elseArm := b.getD #[]
      let condTerm ← evalExpr sc.vars .bool c
      -- What an arm that falls through continues into: the rest of this
      -- list, and only then the enclosing continuation.
      let after : Cont := lowerStmts fresh sc rest k
      let n ← fresh.modifyGet fun n => (n, n + 1)
      let condId := mkIdent (Name.mkSimple s!"ts#cond{n}")
      let ruledOut : Cont :=
        throwErrorAt s "the lowering reached an arm it had ruled out"
      let mut joinBinding : Option (Ident × TSyntax `term) := none
      let mut thenK : Cont := ruledOut
      let mut elseK : Cont := ruledOut
      if stmtsLeave a && stmtsLeave elseArm then
        -- Both arms leave: the tail is unreachable, so it is never built.
        pure ()
      else if stmtsLeave a then
        elseK := after
      else if stmtsLeave elseArm then
        thenK := after
      else
        -- Both arms fall through, so the tail has two callers. Binding it
        -- to a function of the names the arms may have reassigned joins
        -- the branches without writing the tail out twice.
        let joins := (assignedIn sc.muts a ++ assignedIn sc.muts elseArm).eraseDups
        let joinId := mkIdent (Name.mkSimple s!"ts#join{n}")
        let jump : Cont := do
          let mut call : TSyntax `term ← `($joinId)
          for j in joins do
            call ← `($call $(mkIdent (Name.mkSimple j)))
          `(($call : JsM Float))
        let lam ← joins.foldrM (init := ← after) fun j acc =>
          `(fun ($(mkIdent (Name.mkSimple j)) : Float) => $acc)
        joinBinding := some (joinId, lam)
        thenK := jump
        elseK := jump
      let thenTerm ← lowerStmts fresh sc a.toList thenK
      let elseTerm ← lowerStmts fresh sc elseArm.toList elseK
      let branch ←
        `(((($condTerm) >>= fun $condId =>
              bif $condId then $thenTerm else $elseTerm) : JsM Float))
      match joinBinding with
      | some (joinId, lam) => `((let $joinId:ident := $lam; $branch))
      | none => pure branch
    | `(ts_stmt| ts.opaque[$kind:str]($line:num, $col:num)) =>
      throwErrorAt kind (unmappedMsg kind.getString s!"{line.getNat}:{col.getNat}")
    | stx => throwErrorAt stx "unsupported statement shape"

/-- The namespace under which models are declared. -/
def modelNamespace : Name := `TsModel

/-- `Float → ... → Float → JsM Float` with `arity` arrows. -/
def mkModelType (arity : Nat) : CommandElabM (TSyntax `term) := do
  let mut ty ← `(JsM Float)
  for _ in List.range arity do
    ty ← `(Float → $ty)
  pure ty

elab_rules : command
  | `(ts_def $name:str := ts.opaque[$kind:str]($line:num, $col:num)) => do
    let pos := s!"{line.getNat}:{col.getNat}"
    modifyEnv fun env =>
      failedExt.addEntry env
        ⟨name.getString, some kind.getString, unmappedMsg kind.getString pos⟩

elab_rules : command
  | `(ts_def $name:str := ts.fn($params:ts_param,*) : ts.number {$stmts:ts_stmt*}) => do
    let recordFailure (construct : Option String) (reason : String) : CommandElabM Unit :=
      modifyEnv fun env => failedExt.addEntry env ⟨name.getString, construct, reason⟩
    -- Lean prints diagnostics to stdout — the verdict channel — so per-
    -- declaration containment must be silent: the failure is recorded and
    -- surfaces in the verdicts of the annotations over this declaration.
    if let some (construct, pos) := stmts.raw.findSome? findOpaque? then
      return ← recordFailure (some construct) (unmappedMsg construct pos)
    if let some (op, reason) := stmts.raw.findSome? findUnmodeledOp? then
      return ← recordFailure (some op) reason
    -- A body that calls a declaration outside the model is outside it too,
    -- and for the same construct: an imported name the transcriber could
    -- not follow is the input's business, not a broken elaboration.
    let called := stmts.raw.toList.flatMap callNames
    if let some (construct, reason) := calleeFailure? (← getEnv) called then
      return ← recordFailure (some construct) reason
    try
      let paramNames ← params.getElems.mapM fun p => do
        match p with
        | `(ts_param| ts.param[$x:str](ts.number)) => pure x.getString
        | _ => throwErrorAt p "unsupported parameter shape"
      -- Parameters are assignable: JavaScript lets a body rebind one, and
      -- rebinding here is shadowing, so it costs the lowering nothing.
      let scope : Scope := { vars := paramNames.toList, muts := paramNames.toList }
      let fresh ← IO.mkRef 0
      -- A `number` function that runs off the end returns undefined, which
      -- this slice has no value for: the declaration degrades instead.
      let bodyTerm ← lowerStmts fresh scope stmts.toList
        (throwErrorAt name "the body must return on every path")
      let declName := modelNamespace ++ Name.mkSimple name.getString
      let declId := mkIdent declName
      let ty ← mkModelType paramNames.size
      let fn ← paramNames.foldrM (init := bodyTerm) fun x acc =>
        `(fun ($(mkIdent (Name.mkSimple x)) : Float) => $acc)
      -- elabCommand logs failures instead of throwing; treat new errors as
      -- this declaration's failure and swallow them.
      let savedMsgs := (← get).messages
      -- Dual-tagged: the simp closers and the grind rung both unfold
      -- models by their equations.
      elabCommand (← `(@[js_norm, grind] def $declId : $ty := $fn))
      if (← get).messages.hasErrors && !savedMsgs.hasErrors then
        modify fun s => { s with messages := savedMsgs }
        recordFailure none "the model definition did not elaborate"
      else
        modifyEnv fun env =>
          modelExt.addEntry env ⟨name.getString, declName, paramNames.size⟩
    catch ex =>
      recordFailure none (← ex.toMessageData.toString)

end ThalesDsl
