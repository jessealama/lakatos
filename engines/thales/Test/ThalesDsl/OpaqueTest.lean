import ThalesDsl.Model

open Lean ThalesDsl

-- An opaque node in expression position degrades the declaration alone: it
-- is recorded as failed with the construct name, registers no model, and
-- the build stays clean.
ts_def "halts" := ts.fn(ts.param["p"](ts.number)) : ts.number {
  ts.return(ts.opaque["AwaitExpression"](7, 3))
}

-- Opaque in statement position, alongside mappable statements.
ts_def "spin" := ts.fn(ts.param["n"](ts.number)) : ts.number {
  ts.opaque["WhileStatement"](12, 3)
  ts.return(ts.id["n"])
}

-- A non-opaque failure (unbound identifier) is contained the same way but
-- records no construct.
ts_def "oops" := ts.fn() : ts.number { ts.return(ts.id["ghost"]) }

-- A whole declaration the front end cannot shape as ts.fn (a class, a
-- const-arrow, an inexpressible signature) arrives as an opaque ts_def:
-- named, failed, construct recorded.
ts_def "Point#norm" := ts.opaque["ClassDeclaration"](4, 1)

-- Later declarations elaborate normally.
ts_def "after" := ts.fn() : ts.number { ts.return(ts.num[5]) }
#guard decide (TsModel.after = (pure 5.0 : TsM Float))

#eval show CoreM Unit from do
  let env ← getEnv
  let some halts := findFailed? env "halts"
    | throwError "'halts' should be recorded as failed"
  unless halts.construct == some "AwaitExpression" do
    throwError "'halts' should record its unmapped construct, got {repr halts.construct}"
  let some spin := findFailed? env "spin"
    | throwError "'spin' should be recorded as failed"
  unless spin.construct == some "WhileStatement" do
    throwError "'spin' should record its unmapped construct, got {repr spin.construct}"
  let some oops := findFailed? env "oops"
    | throwError "'oops' should be recorded as failed"
  unless oops.construct == none do
    throwError "'oops' is not an opaque failure, got {repr oops.construct}"
  let some norm := findFailed? env "Point#norm"
    | throwError "'Point#norm' should be recorded as failed"
  unless norm.construct == some "ClassDeclaration" do
    throwError "'Point#norm' should record its unmapped construct, got {repr norm.construct}"
  unless norm.reason == unmappedMsg "ClassDeclaration" "4:1" do
    throwError "'Point#norm' reason should carry the position, got {norm.reason}"
  for tsName in ["halts", "spin", "oops", "Point#norm"] do
    unless (findModel? env tsName).isNone do
      throwError "failed declaration '{tsName}' must register no model"
  unless (findFailed? env "after").isNone do
    throwError "'after' should not be recorded as failed"
