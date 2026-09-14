import Test.ThalesEmit.Support

/-! The correspondence command the emitter writes, one guard per shape it
can take: which declarations get an obligation, what the obligation says,
and the reason a declaration that gets none carries instead.

The guards compare trees, not text, so the pretty-printer is out of the
loop — except for the last check, which prints the tracer's command and
parses it back. The artifact is re-parsed plain text, so what the printer
lays out has to be a `command`; that is the property, not a layout. -/

open Lean ThalesEmit

private def nums (names : Array String) : Array Param :=
  names.map fun n => { name := n, ty := .number }

/-- A closure that is present and decoded. Its contents never reach the
obligation — the term names the `.ast` def, which `Ast.lean` prints — so
the empty script stands for every decoded closure here. -/
private def closed : Option DeclAst := some (.program [])

private def plans (e : Emission) (f : EmitFn) (expected : Unhygienic Term) : Bool :=
  rendersSyntax (do
    match ← fnPlan e f with
    | .obligation t => pure t
    | .bare r => throw s!"bare: {r}"
    | .none => throw "no command") expected

private def bares (e : Emission) (f : EmitFn) (reason : String) : Bool :=
  match RenderM.run (fnPlan e f) with
  | .ok (.bare r) => r == reason
  | _ => false

private def lone (f : EmitFn) : Emission :=
  { file := "t.ts", declarations := #[.fn f], obligations := #[] }

-- The tracer's `add`, the issue's own example: the closure, then a call
-- with the quantified arguments spliced in as `.numLit`, projected
-- through the number reader against the model applied to the same.
#guard plans
  (lone { name := "add", params := nums #["a", "b"], source := "add",
          body := #[.ret (.binop "+" (.id "a") (.id "b"))], ast := closed })
  { name := "add", params := nums #["a", "b"], source := "add",
    body := #[.ret (.binop "+" (.id "a") (.id "b"))], ast := closed }
  `(∀ (a b : JsNumber),
      Tarski.project Tarski.readNumber
          (Tarski.runScript
            (TsModel.add.ast ++ [.exprStmt (.call (.ident "add") [.numLit a, .numLit b])]))
        = some (Tarski.Outcome.ofModel (TsModel.add a b)))

-- A boolean parameter is a `.boolLit`, and a boolean return reads through
-- `Tarski.readBool`.
private def isSmall : EmitFn :=
  { name := "isSmall", returns := .bool, params := #[{ name := "b", ty := .bool }],
    source := "isSmall", body := #[.ret (.id "b")], ast := closed }

#guard plans (lone isSmall) isSmall
  `(∀ (b : Bool),
      Tarski.project Tarski.readBool
          (Tarski.runScript
            (TsModel.isSmall.ast ++ [.exprStmt (.call (.ident "isSmall") [.boolLit b])]))
        = some (Tarski.Outcome.ofModel (TsModel.isSmall b)))

-- No parameters, no `∀`: the obligation is a closed equation.
private def zero : EmitFn :=
  { name := "one", params := #[], source := "one", body := #[.ret (.num "1")],
    ast := closed }

#guard plans (lone zero) zero
  `(Tarski.project Tarski.readNumber
      (Tarski.runScript (TsModel.one.ast ++ [.exprStmt (.call (.ident "one") [])]))
    = some (Tarski.Outcome.ofModel TsModel.one))

-- A reserved parameter spelling is primed in the binder, in the literal,
-- and at the model's application — but the call names the function by its
-- JS spelling, which is a string and cannot be captured.
private def primed : EmitFn :=
  { name := "pure", params := nums #["self"], source := "pure",
    body := #[.ret (.id "self")], ast := closed }

#guard plans (lone primed) primed
  `(∀ (self' : JsNumber),
      Tarski.project Tarski.readNumber
          (Tarski.runScript
            (TsModel.pure.ast ++ [.exprStmt (.call (.ident "pure") [.numLit self'])]))
        = some (Tarski.Outcome.ofModel (TsModel.pure self')))

-- A module constant: the closure, then a read of the name. Its model is a
-- `JsNumber` and not a `JsM`, so the right-hand side is `Outcome.value`.
#guard rendersSyntax (do
    match ← constPlan { name := "K", init := .num "60", source := "K", ast := closed } with
    | .obligation t => pure t
    | _ => throw "no obligation")
  `(Tarski.project Tarski.readNumber
      (Tarski.runScript (TsModel.K.ast ++ [.exprStmt (.ident "K")]))
    = some (Tarski.Outcome.value TsModel.K))

-- A tainted function names the construct its own residual refused.
#guard bares
  { file := "t.ts"
    declarations := #[
      .residual { owner := "f", site := 1, construct := "'**' is not supported",
                  params := nums #["x"], ty := .number },
      .fn { name := "f", params := nums #["x"], source := "f", tainted := true,
            body := #[.ret (.residual "f" none 1 #[.id "x"])], ast := closed }]
    obligations := #[] }
  { name := "f", params := nums #["x"], source := "f", tainted := true,
    body := #[.ret (.residual "f" none 1 #[.id "x"])], ast := closed }
  "'**' is not supported"

-- Tainted through a callee: the site belongs to the callee, so the walk
-- follows the call and reports the callee's constructs, joined the way an
-- `Inappropriate` verdict joins its sites.
private def twoSites : Emission :=
  { file := "t.ts"
    declarations := #[
      .residual { owner := "g", site := 1, construct := "'**' is not supported",
                  params := nums #["x"], ty := .number },
      .residual { owner := "g", site := 2, construct := "'double' could not be modeled",
                  params := nums #["x"], ty := .number },
      .fn { name := "g", params := nums #["x"], source := "g", tainted := true,
            body := #[.ret (.residual "g" none 1 #[.residual "g" none 2 #[.id "x"]])] },
      .fn { name := "f", params := nums #["x"], source := "f", tainted := true,
            body := #[.ret (.call "g" none #[.id "x"])], ast := closed }]
    obligations := #[] }

#guard bares twoSites
  { name := "f", params := nums #["x"], source := "f", tainted := true,
    body := #[.ret (.call "g" none #[.id "x"])], ast := closed }
  "'**' is not supported; 'double' could not be modeled"

-- A taint whose site the walk cannot reach still says something true.
#guard bares
  (lone { name := "f", params := #[], source := "f", tainted := true,
          body := #[.ret (.num "1")], ast := closed })
  { name := "f", params := #[], source := "f", tainted := true,
    body := #[.ret (.num "1")], ast := closed }
  "'f' reaches code outside the model"

-- No closure, and a closure the decoder refused.
#guard bares (lone { name := "f", params := #[], source := "f", body := #[.ret (.num "1")] })
  { name := "f", params := #[], source := "f", body := #[.ret (.num "1")] }
  "the closure of 'f' is not a closed script"

#guard bares
  (lone { name := "f", params := #[], source := "f", body := #[.ret (.num "1")],
          ast := some (.unsupported "FunctionDeclaration async") })
  { name := "f", params := #[], source := "f", body := #[.ret (.num "1")],
    ast := some (.unsupported "FunctionDeclaration async") }
  "unsupported: FunctionDeclaration async"

-- A parameter this slice cannot quantify: a union needs a literal map and
-- a tag split, an option and a class instance are #482's.
private def withParam (ty : ParamTy) : EmitFn :=
  { name := "f", params := #[{ name := "x", ty }], source := "f",
    body := #[.ret (.num "1")], ast := closed }

#guard bares (lone (withParam (.union #[.number, .string]))) (withParam (.union #[.number, .string]))
  "parameter 'x' of 'f' is not a number or boolean"
#guard bares (lone (withParam (.option "Box" none))) (withParam (.option "Box" none))
  "parameter 'x' of 'f' is not a number or boolean"
#guard bares (lone (withParam (.cls "Box" none))) (withParam (.cls "Box" none))
  "parameter 'x' of 'f' is not a number or boolean"

-- A dependency's declaration gets no command at all.
#guard
  match RenderM.run (fnPlan (lone zero)
      { name := "double", module := some "helper.mts", params := nums #["x"],
        source := "double", body := #[.ret (.id "x")], ast := closed }) with
  | .ok .none => true
  | _ => false

-- The artifact carries the command as text a later `lake env lean` run
-- parses, so the printed form has to be a `command`. The tracer's shape
-- is the one the goldens show.
open Elab Command in
#eval show CommandElabM Unit from do
  let cmd ← liftCoreM do
    match RenderM.run (do
        validateCommand "t.ts" "add" (← fnPlan
          (lone { name := "add", params := nums #["a", "b"], source := "add",
                  body := #[.ret (.binop "+" (.id "a") (.id "b"))], ast := closed })
          { name := "add", params := nums #["a", "b"], source := "add",
            body := #[.ret (.binop "+" (.id "a") (.id "b"))], ast := closed })) with
    | .error msg => throwError msg
    | .ok none => throwError "the entry function got no command"
    | .ok (some c) => pure (prettyLines (← PrettyPrinter.ppCommand ⟨unscope c.raw⟩))
  match Parser.runParserCategory (← getEnv) `command cmd with
  | .error e => throwError "the printed command does not parse: {e}\n{cmd}"
  | .ok _ => pure ()
