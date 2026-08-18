import Lean
import ThalesDsl.TsM
import ThalesDsl.Syntax

namespace ThalesDsl

open Lean Elab Command

/-- A registered TS function model. This slice types every parameter and
result as `Int`, so arity is the whole signature. -/
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

/-- The value types of the slice. Expression elaboration is type-directed:
the operator decides its operand and result types. -/
inductive ValTy where
  | int
  | bool
deriving BEq, Repr

def ValTy.describe : ValTy → String
  | .int => "a number"
  | .bool => "a boolean"

def tsIntLitToTerm : TSyntax ``tsIntLit → CommandElabM (TSyntax `term)
  | `(tsIntLit| $n:num) => `(($n : Int))
  | `(tsIntLit| -$n:num) => `((-$n : Int))
  | stx => throwErrorAt stx "malformed integer literal"

/-- `ts#argN`: cannot capture, since `#` never occurs in a TS identifier. -/
def freshArg (i : Nat) : Ident := mkIdent (Name.mkSimple s!"ts#arg{i}")

/-- Transcribes a `ts_expr` into a Lean term of type `TsM Int` /
`TsM Bool` per `expected`. Registry misses and operator/type mismatches
throw here, so `#thales_prove` can contain them per command. -/
partial def evalExpr (vars : List String) (expected : ValTy) :
    TSyntax `ts_expr → CommandElabM (TSyntax `term)
  | `(ts_expr| ts.num[$n:tsIntLit]) => do
    unless expected == .int do
      throwErrorAt n "a numeric literal cannot be {expected.describe}"
    `((pure $(← tsIntLitToTerm n) : TsM Int))
  | `(ts_expr| ts.id[$x:str]) => do
    unless vars.contains x.getString do
      throwErrorAt x "unbound identifier '{x.getString}'"
    unless expected == .int do
      throwErrorAt x "identifier '{x.getString}' is a number, not {expected.describe}"
    `((pure $(mkIdent (Name.mkSimple x.getString)) : TsM Int))
  | `(ts_expr| ts.binop[$op:str]($l:ts_expr, $r:ts_expr)) => do
    let lt ← evalExpr vars .int l
    let rt ← evalExpr vars .int r
    -- The combining lambda is interpolated into the same quotation that
    -- binds the operands, keeping hygiene consistent.
    let arith (f : TSyntax `term) : CommandElabM (TSyntax `term) := do
      unless expected == .int do
        throwErrorAt op "operator '{op.getString}' yields a number, not {expected.describe}"
      `((($lt >>= fun a => $rt >>= fun b => pure ($f a b)) : TsM Int))
    let cmp (f : TSyntax `term) : CommandElabM (TSyntax `term) := do
      unless expected == .bool do
        throwErrorAt op "operator '{op.getString}' yields a boolean, not {expected.describe}"
      `((($lt >>= fun a => $rt >>= fun b => pure (decide ($f a b))) : TsM Bool))
    match op.getString with
    | "+" => arith (← `(fun x y => x + y))
    | "-" => arith (← `(fun x y => x - y))
    | "*" => arith (← `(fun x y => x * y))
    | "<" => cmp (← `(fun x y => x < y))
    | "<=" => cmp (← `(fun x y => x ≤ y))
    | ">" => cmp (← `(fun x y => x > y))
    | ">=" => cmp (← `(fun x y => x ≥ y))
    | "===" => cmp (← `(fun x y => x = y))
    | "!==" => cmp (← `(fun x y => x ≠ y))
    | other => throwErrorAt op "operator '{other}' has no model in this slice"
  | `(ts_expr| ts.call[$f:str]($args:ts_expr,*)) => do
    let some info := findModel? (← getEnv) f.getString
      | throwErrorAt f "no model registered for '{f.getString}'"
    unless info.arity == args.getElems.size do
      throwErrorAt f
        "'{f.getString}' expects {info.arity} argument(s), got {args.getElems.size}"
    unless expected == .int do
      throwErrorAt f "a call to '{f.getString}' yields a number, not {expected.describe}"
    let argTerms ← args.getElems.mapM (evalExpr vars .int)
    let argNames := (List.range argTerms.size).map freshArg
    let mut call : TSyntax `term ← `($(mkIdent info.declName))
    for n in argNames do
      call ← `($call $n)
    let mut body ← `(($call : TsM Int))
    for (name, arg) in (argNames.zip argTerms.toList).reverse do
      body ← `((($arg >>= fun $name => $body) : TsM Int))
    pure body
  | stx => throwErrorAt stx "unsupported expression shape"

/-- The namespace under which models are declared. -/
def modelNamespace : Name := `TsModel

/-- `Int → ... → Int → TsM Int` with `arity` arrows. -/
def mkModelType (arity : Nat) : CommandElabM (TSyntax `term) := do
  let mut ty ← `(TsM Int)
  for _ in List.range arity do
    ty ← `(Int → $ty)
  pure ty

elab_rules : command
  | `(ts_def $name:str := ts.fn($params:ts_param,*) : ts.number {$stmts:ts_stmt*}) => do
    let paramNames ← params.getElems.mapM fun p => do
      match p with
      | `(ts_param| ts.param[$x:str](ts.number)) => pure x.getString
      | _ => throwErrorAt p "unsupported parameter shape"
    -- Slice: the body is exactly one return statement.
    let #[stmt] := stmts.raw | throwErrorAt name "the body must be a single return statement"
    let `(ts_stmt| ts.return($e:ts_expr)) := stmt
      | throwErrorAt stmt "unsupported statement shape"
    let bodyTerm ← evalExpr paramNames.toList .int e
    let declName := modelNamespace ++ Name.mkSimple name.getString
    let declId := mkIdent declName
    let ty ← mkModelType paramNames.size
    let fn ← paramNames.foldrM (init := bodyTerm) fun x acc =>
      `(fun ($(mkIdent (Name.mkSimple x)) : Int) => $acc)
    elabCommand (← `(def $declId : $ty := $fn))
    modifyEnv fun env =>
      modelExt.addEntry env ⟨name.getString, declName, paramNames.size⟩

end ThalesDsl
