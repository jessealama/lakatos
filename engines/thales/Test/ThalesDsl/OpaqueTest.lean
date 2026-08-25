import ThalesDsl.Model

open Lean ThalesDsl Js Js.Number

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

-- A body calling a declaration that failed on a construct fails on that
-- same construct: the caller is outside the model because what it calls is.
ts_def "caller" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.return(ts.call["Point#norm"](ts.id["x"]))
}

-- A callee that failed for some other reason leaves the caller's failure
-- unnamed: that one is the engine's business, not the input's.
ts_def "callsOops" := ts.fn() : ts.number { ts.return(ts.call["oops"]()) }

-- Later declarations elaborate normally.
ts_def "after" := ts.fn() : ts.number { ts.return(ts.num[5]) }
#guard decide (TsModel.after = (pure 5.0 : JsM Float))

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
  let some caller := findFailed? env "caller"
    | throwError "'caller' should be recorded as failed"
  unless caller.construct == some "ClassDeclaration" do
    throwError "'caller' should inherit its callee's construct, got {repr caller.construct}"
  unless (caller.reason.splitOn "'Point#norm'").length > 1 do
    throwError "'caller' should name the callee it failed on, got {caller.reason}"
  let some callsOops := findFailed? env "callsOops"
    | throwError "'callsOops' should be recorded as failed"
  unless callsOops.construct == none do
    throwError "'callsOops' names no construct, got {repr callsOops.construct}"
  for tsName in ["halts", "spin", "oops", "Point#norm", "caller", "callsOops"] do
    unless (findModel? env tsName).isNone do
      throwError "failed declaration '{tsName}' must register no model"
  unless (findFailed? env "after").isNone do
    throwError "'after' should not be recorded as failed"
