import Lean
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

/-- A declaration whose `ts_def` failed to elaborate. `construct` is the
unmapped TypeScript construct when the failure came from an opaque node;
`none` means some other elaboration failure. -/
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

/-- Every function name `stx` calls, in tree order. -/
partial def callNames (stx : Syntax) : List String :=
  let here := match stx with
    | `(ts_expr| ts.call[$f:str]($_args:ts_expr,*)) => [f.getString]
    | _ => []
  here ++ stx.getArgs.toList.flatMap callNames

/-- Why `p` cannot be attempted under the containment contract: an opaque
node in the formula itself, or a call to a declaration whose `ts_def`
failed on an unmapped construct. `none` means the formula may elaborate. -/
def propInappropriate? (env : Environment) (p : TSyntax `ts_prop) : Option String :=
  match findOpaque? p.raw with
  | some (construct, pos) => some (unmappedMsg construct pos)
  | none =>
    (callNames p.raw).findSome? fun n =>
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

/-- A numeric literal in a program body is a binary64 value. Lean's literal
rounding agrees with JavaScript's, so a literal too large to represent
lands on the same double either language would choose. -/
def tsIntLitToFloat : TSyntax ``tsIntLit → CommandElabM (TSyntax `term)
  | `(tsIntLit| $n:num) => `(($n : Float))
  | `(tsIntLit| -$n:num) => `((-$n : Float))
  | stx => throwErrorAt stx "malformed integer literal"

/-- `ts#argN`: cannot capture, since `#` never occurs in a TS identifier. -/
def freshArg (i : Nat) : Ident := mkIdent (Name.mkSimple s!"ts#arg{i}")

/-- Transcribes a `ts_expr` into a Lean term of type `TsM Float` /
`TsM Bool` per `expected`. Registry misses and operator/type mismatches
throw here, so `#thales_prove` can contain them per command. -/
partial def evalExpr (vars : List String) (expected : ValTy) :
    TSyntax `ts_expr → CommandElabM (TSyntax `term)
  | `(ts_expr| ts.num[$n:tsIntLit]) => do
    unless expected == .num do
      throwErrorAt n "a numeric literal cannot be {expected.describe}"
    `((pure $(← tsIntLitToFloat n) : TsM Float))
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
    | "<" => cmp (← `(fun x y => Float.lt x y))
    | "<=" => cmp (← `(fun x y => Float.le x y))
    | ">" => cmp (← `(fun x y => Float.lt y x))
    | ">=" => cmp (← `(fun x y => Float.le y x))
    | "===" => cmp (← `(fun x y => Float.beq x y))
    | "!==" => cmp (← `(fun x y => !Float.beq x y))
    | other => throwErrorAt op "operator '{other}' has no model in this slice"
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
    try
      let paramNames ← params.getElems.mapM fun p => do
        match p with
        | `(ts_param| ts.param[$x:str](ts.number)) => pure x.getString
        | _ => throwErrorAt p "unsupported parameter shape"
      -- Slice: the body is exactly one return statement.
      let #[stmt] := stmts.raw | throwErrorAt name "the body must be a single return statement"
      let `(ts_stmt| ts.return($e:ts_expr)) := stmt
        | throwErrorAt stmt "unsupported statement shape"
      let bodyTerm ← evalExpr paramNames.toList .num e
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
