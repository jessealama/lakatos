import ThalesDsl.Prove

open ThalesDsl Js Js.Number

-- Statement lowering: a body is a statement tree, and every statement list
-- in it — arms included — lowers to one `JsM Float` expression.

-- An `if` with no else: the then arm returns, and the rest of the body is
-- the else arm's continuation.
ts_def "clamp" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.if(ts.binop["<"](ts.id["x"], ts.num[0])) {
    ts.return(ts.num[0])
  }
  ts.return(ts.id["x"])
}
#guard decide (TsModel.clamp (-3.0) = (pure 0.0 : JsM Float))
#guard decide (TsModel.clamp 3.0 = (pure 3.0 : JsM Float))

-- Both arms return: there is no tail to continue into.
ts_def "sign" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.if(ts.binop["<"](ts.id["x"], ts.num[0])) {
    ts.return(ts.num[-1])
  } else {
    ts.return(ts.num[1])
  }
}
#guard decide (TsModel.sign (-3.0) = (pure (-1.0) : JsM Float))
#guard decide (TsModel.sign 3.0 = (pure 1.0 : JsM Float))

-- ts.throw leaves its path, carrying the error kind alone.
ts_def "recip" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.if(ts.binop["==="](ts.id["x"], ts.num[0])) {
    ts.throw["RangeError"]
  }
  ts.return(ts.binop["/"](ts.num[1], ts.id["x"]))
}
#guard decide (TsModel.recip 0.0 = (JsM.throw (.error "RangeError") : JsM Float))
#guard decide (TsModel.recip 4.0 = (pure 0.25 : JsM Float))

-- A throwing condition throws before either arm runs.
ts_def "viaRecip" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.if(ts.binop["<"](ts.call["recip"](ts.id["x"]), ts.num[1])) {
    ts.return(ts.num[0])
  }
  ts.return(ts.num[1])
}
#guard decide (TsModel.viaRecip 0.0 = (JsM.throw (.error "RangeError") : JsM Float))
#guard decide (TsModel.viaRecip 4.0 = (pure 0.0 : JsM Float))
#guard decide (TsModel.viaRecip 0.5 = (pure 1.0 : JsM Float))

-- A `ts.let` reassigned in both arms: the tail reads the joined binding.
ts_def "bump" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.let["y"](ts.num[0])
  ts.if(ts.binop[">"](ts.id["x"], ts.num[10])) {
    ts.assign["y"](ts.num[1])
  } else {
    ts.assign["y"](ts.num[2])
  }
  ts.return(ts.binop["+"](ts.id["y"], ts.id["x"]))
}
#guard decide (TsModel.bump 20.0 = (pure 21.0 : JsM Float))
#guard decide (TsModel.bump 1.0 = (pure 3.0 : JsM Float))

-- An arm that does not assign carries the initializer through the join.
ts_def "bumpOne" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.let["y"](ts.num[5])
  ts.if(ts.binop[">"](ts.id["x"], ts.num[10])) {
    ts.assign["y"](ts.num[1])
  }
  ts.return(ts.id["y"])
}
#guard decide (TsModel.bumpOne 20.0 = (pure 1.0 : JsM Float))
#guard decide (TsModel.bumpOne 1.0 = (pure 5.0 : JsM Float))

-- Several names join at once, each arm reading the values it entered with.
ts_def "shuffle" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.let["a"](ts.num[1])
  ts.let["b"](ts.num[2])
  ts.if(ts.binop[">"](ts.id["x"], ts.num[0])) {
    ts.assign["a"](ts.id["b"])
    ts.assign["b"](ts.num[3])
  }
  ts.return(ts.binop["+"](ts.binop["*"](ts.id["a"], ts.num[10]), ts.id["b"]))
}
#guard decide (TsModel.shuffle 1.0 = (pure 23.0 : JsM Float))
#guard decide (TsModel.shuffle (-1.0) = (pure 12.0 : JsM Float))

-- An `else if` chain, whose middle arm both returns on one path and falls
-- through on another: the arms disagree about leaving, and the tail is
-- still written once.
ts_def "ladder" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.let["y"](ts.num[0])
  ts.if(ts.binop["<"](ts.id["x"], ts.num[0])) {
    ts.return(ts.num[-1])
  } else {
    ts.if(ts.binop["<"](ts.id["x"], ts.num[10])) {
      ts.assign["y"](ts.num[1])
    } else {
      ts.assign["y"](ts.num[2])
    }
  }
  ts.return(ts.binop["+"](ts.id["y"], ts.num[100]))
}
#guard decide (TsModel.ladder (-1.0) = (pure (-1.0) : JsM Float))
#guard decide (TsModel.ladder 5.0 = (pure 101.0 : JsM Float))
#guard decide (TsModel.ladder 50.0 = (pure 102.0 : JsM Float))

-- A parameter is assignable, the way JavaScript has it.
ts_def "atLeastOne" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.if(ts.binop["<"](ts.id["x"], ts.num[1])) {
    ts.assign["x"](ts.num[1])
  }
  ts.return(ts.id["x"])
}
#guard decide (TsModel.atLeastOne 0.5 = (pure 1.0 : JsM Float))
#guard decide (TsModel.atLeastOne 4.0 = (pure 4.0 : JsM Float))

-- A body that can run off the end has no value to return; the declaration
-- degrades rather than inventing one.
ts_def "noReturn" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.if(ts.binop["<"](ts.id["x"], ts.num[0])) {
    ts.return(ts.num[0])
  }
}

-- Only a `ts.let` is assignable; a const is not.
ts_def "constAssign" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.const["y"](ts.num[1])
  ts.assign["y"](ts.num[2])
  ts.return(ts.id["y"])
}

-- An arm's own binding would capture the joined name it shadows, so a
-- redeclaration is refused rather than lowered.
ts_def "shadowed" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.let["y"](ts.num[1])
  ts.if(ts.binop[">"](ts.id["x"], ts.num[0])) {
    ts.const["y"](ts.num[2])
    ts.assign["y"](ts.num[3])
  }
  ts.return(ts.id["y"])
}

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for name in ["noReturn", "constAssign", "shadowed"] do
    unless (findModel? env name).isNone do
      throwError "'{name}' should not register a model"
    let some failed := findFailed? env name
      | throwError "'{name}' should be recorded as failed"
    -- Nothing here is an unmapped construct: the input is TypeScript the
    -- model does cover, so these stay engine-side failures.
    unless failed.construct == none do
      throwError "'{name}' should not name a construct, got {repr failed.construct}"

-- An opaque statement anywhere in the tree degrades the declaration,
-- naming the construct, however deep in a branch it sits.
ts_def "looped" := ts.fn(ts.param["x"](ts.number)) : ts.number {
  ts.if(ts.binop["<"](ts.id["x"], ts.num[0])) {
    ts.opaque["ForStatement"](3, 5)
  }
  ts.return(ts.id["x"])
}

open Lean in
#eval show CoreM Unit from do
  let some failed := findFailed? (← getEnv) "looped"
    | throwError "'looped' should be recorded as failed"
  unless failed.construct == some "ForStatement" do
    throwError "'looped' should name the loop, got {repr failed.construct}"

-- The verdicts a branching body earns. A bounded domain settles by
-- evaluation; an unbounded one needs the branch condition as a hypothesis
-- on the arm it selects, plus the totality of IEEE comparison away from
-- NaN, which the binder's infinity bounds establish.
#thales_prove "s.ts" "clamp" "nonnegBounded" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(-10, 10))) {
    ts.istrue(ts.binop[">="](ts.call["clamp"](ts.id["x"]), ts.num[0]))
  }

#thales_prove "s.ts" "clamp" "nonneg" :=
  ts.forall(ts.binder["x"](ts.number, ts.lower["<"](ts.fnum[-Infinity]),
      ts.upper["<"](ts.fnum[Infinity]))) {
    ts.istrue(ts.binop[">="](ts.call["clamp"](ts.id["x"]), ts.num[0]))
  }

-- A guard that excludes the throwing branch proves; a domain that reaches
-- the throw does not, and the witness is the argument that throws.
#thales_prove "s.ts" "recip" "guarded" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(1, 5))) {
    ts.imp(ts.binop[">"](ts.id["x"], ts.num[0])) {
      ts.istrue(ts.binop[">"](ts.call["recip"](ts.id["x"]), ts.num[0]))
    }
  }

#thales_prove "s.ts" "recip" "unguarded" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(0, 5))) {
    ts.istrue(ts.binop[">"](ts.call["recip"](ts.id["x"]), ts.num[0]))
  }

-- A joined binding survives into the property.
#thales_prove "s.ts" "bumpOne" "positive" :=
  ts.forall(ts.binder["x"](ts.int, ts.range(-5, 20))) {
    ts.istrue(ts.binop[">"](ts.call["bumpOne"](ts.id["x"]), ts.num[0]))
  }
