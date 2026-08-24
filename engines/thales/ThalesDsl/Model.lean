import Lean
import ThalesDsl.FloatOps
import ThalesDsl.TsM
import ThalesDsl.Norm
import ThalesDsl.Syntax

namespace ThalesDsl

open Lean Elab Command

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

/-- Why `p` cannot be attempted under the containment contract: an opaque
node or a refused operator in the formula itself, or a call to a declaration
whose `ts_def` failed on one. `none` means the formula may elaborate. -/
def propInappropriate? (env : Environment) (p : TSyntax `ts_prop) : Option String :=
  (findOpaque? p.raw).map (fun (construct, pos) => unmappedMsg construct pos)
  <|> (findUnmodeledOp? p.raw).map Prod.snd
  <|> (callNames p.raw).findSome? fun n =>
        if (findModel? env n).isSome then none
        else match findFailed? env n with
          | some failed =>
            if failed.construct.isSome then
              some s!"'{n}' could not be modeled: {failed.reason}"
            else none
          | none => none

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

/-- Transcribes a `ts_expr` into a Lean term of type `TsM Float` /
`TsM Bool` per `expected`. Registry misses and operator/type mismatches
throw here, so `#thales_prove` can contain them per command. -/
partial def evalExpr (vars : List String) (expected : ValTy) :
    TSyntax `ts_expr → CommandElabM (TSyntax `term)
  | `(ts_expr| ts.num[$n:tsFloatLit]) => do
    unless expected == .num do
      throwErrorAt n "a numeric literal cannot be {expected.describe}"
    `((pure $(← tsFloatLitToTerm n) : TsM Float))
  | `(ts_expr| ts.id[$x:str]) => do
    unless vars.contains x.getString do
      throwErrorAt x "unbound identifier '{x.getString}'"
    unless expected == .num do
      throwErrorAt x "identifier '{x.getString}' is a number, not {expected.describe}"
    `((pure $(mkIdent (Name.mkSimple x.getString)) : TsM Float))
  | `(ts_expr| ts.binop[$op:str]($l:ts_expr, $r:ts_expr)) => do
    let lt ← evalExpr vars .num l
    let rt ← evalExpr vars .num r
    -- The combining lambda is interpolated into the same quotation that
    -- binds the operands, keeping hygiene consistent.
    let arith (f : TSyntax `term) : CommandElabM (TSyntax `term) := do
      unless expected == .num do
        throwErrorAt op "operator '{op.getString}' yields a number, not {expected.describe}"
      `((($lt >>= fun a => $rt >>= fun b => pure ($f a b)) : TsM Float))
    -- The comparisons are IEEE predicates, already Bool-valued, so there is
    -- no Prop to `decide` here.
    let cmp (f : TSyntax `term) : CommandElabM (TSyntax `term) := do
      unless expected == .bool do
        throwErrorAt op "operator '{op.getString}' yields a boolean, not {expected.describe}"
      `((($lt >>= fun a => $rt >>= fun b => pure ($f a b)) : TsM Bool))
    match op.getString with
    | "+" => arith (← `(fun x y => x + y))
    | "-" => arith (← `(fun x y => x - y))
    | "*" => arith (← `(fun x y => x * y))
    | "/" => arith (← `(fun x y => x / y))
    | "%" => arith (← `(fun x y => ThalesDsl.FloatOps.tsRem x y))
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
    | "-" => `((($xt >>= fun a => pure (-a)) : TsM Float))
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
    let mut body ← `(($call : TsM Float))
    for (name, arg) in (argNames.zip argTerms.toList).reverse do
      body ← `((($arg >>= fun $name => $body) : TsM Float))
    pure body
  | stx => throwErrorAt stx "unsupported expression shape"

/-- The namespace under which models are declared. -/
def modelNamespace : Name := `TsModel

/-- `Float → ... → Float → TsM Float` with `arity` arrows. -/
def mkModelType (arity : Nat) : CommandElabM (TSyntax `term) := do
  let mut ty ← `(TsM Float)
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
    try
      let paramNames ← params.getElems.mapM fun p => do
        match p with
        | `(ts_param| ts.param[$x:str](ts.number)) => pure x.getString
        | _ => throwErrorAt p "unsupported parameter shape"
      -- Slice: const bindings, then exactly one return. Each binding is a
      -- bind, not a substitution, so an unused initializer still evaluates.
      let shapeMsg := "the body must be const bindings followed by a single return"
      let some retStx := stmts.raw.back? | throwErrorAt name shapeMsg
      let `(ts_stmt| ts.return($e:ts_expr)) := retStx | throwErrorAt retStx shapeMsg
      let mut vars := paramNames.toList
      let mut binds : Array (Name × TSyntax `term) := #[]
      for stmt in stmts.raw.pop do
        let `(ts_stmt| ts.const[$x:str]($init:ts_expr)) := stmt
          | throwErrorAt stmt shapeMsg
        binds := binds.push (Name.mkSimple x.getString, ← evalExpr vars .num init)
        vars := vars ++ [x.getString]
      let mut bodyTerm ← evalExpr vars .num e
      -- Right to left, so the first binding is the outermost bind.
      for (x, initTerm) in binds.reverse do
        bodyTerm ← `((($initTerm >>= fun $(mkIdent x) => $bodyTerm) : TsM Float))
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
      elabCommand (← `(@[thales_norm, grind] def $declId : $ty := $fn))
      if (← get).messages.hasErrors && !savedMsgs.hasErrors then
        modify fun s => { s with messages := savedMsgs }
        recordFailure none "the model definition did not elaborate"
      else
        modifyEnv fun env =>
          modelExt.addEntry env ⟨name.getString, declName, paramNames.size⟩
    catch ex =>
      recordFailure none (← ex.toMessageData.toString)

end ThalesDsl
