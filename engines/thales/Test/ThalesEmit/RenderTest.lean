import Test.ThalesEmit.Support

/-! One guard per rendering rule: the tree the renderer builds against the
tree a person would write, no pretty-printer in the loop. -/

open Lean ThalesEmit

def nums (names : Array String) : Array Param :=
  names.map fun n => { name := n, ty := .number }

-- A parameter the body both rebinds at its top level and assigns is not
-- also rebound `let mut x := x`: the top-level binding is the one the
-- body reads, so a second shadow would only be noise.
#eval show CoreM Unit from do
  let f : EmitFn := {
    name := "f", module := none, source := "",
    params := #[{ name := "x", ty := .number },
                { name := "y", ty := .union #[.number, .undefined] }],
    body := #[
      .letDecl "y" .number
        (.cond (.jsvalEq false (.id "y") (.inject .undefined none))
          (.num "1") (.project .number (.id "y"))),
      .assign "y" (.binop "+" (.id "y") (.id "x")),
      .ret (.id "y")] }
  let cmd ← match RenderM.run (fnCommand f) with
    | .error msg => throwError msg
    | .ok cmd => pure cmd
  let text := toString (← Lean.PrettyPrinter.ppCommand ⟨unscope cmd.raw⟩)
  unless (text.splitOn "let mut y").length == 2 do
    throwError "expected exactly one `let mut y` binding, got:\n{text}"

-- A module constant renders as a dual-tagged JsNumber def, and a read of
-- it as a qualified reference, so no binder can capture it.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[
      .const { name := "cap", lit := "1000", source := "const cap = 1000;" },
      .fn { name := "scale", params := nums #["x"], source := "scale",
            body := #[.ret (.binop "*" (.id "x") (.constRead "cap" none))] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "def TsModel.cap : JsNumber :=").length == 2 do
    throwError "the constant def did not render:\n{rendered}"
  -- Both the constant and the function carry the dual tag.
  unless (rendered.splitOn "@[js_norm, grind]").length == 3 do
    throwError "the constant def is not dual-tagged:\n{rendered}"
  unless (rendered.splitOn "x * TsModel.cap").length == 2 do
    throwError "the constant read is not a qualified reference:\n{rendered}"

-- Emitted defs live under the model namespace: a TS function named
-- after a root-level Lean name (`id`) must still define.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "id", params := nums #["x"], source := "id",
                            body := #[.ret (.id "x")] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "def TsModel.id ").length == 2 do
    throwError "the emitted def is not namespaced:\n{rendered}"

-- The artifact is re-parsed plain text: a binder named after the
-- function it calls must not capture the call.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "bump", params := nums #["x"], source := "bump",
                            body := #[.ret (.binop "+" (.id "x") (.num "1"))] }]
    obligations := #[{ function := "bump", property := "p", formula := "f",
                       payload := .structured #[.int "bump"] #[]
                         (.eq (.call "bump" none #[.id "bump"])
                              (.call "bump" none #[.id "bump"])) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "TsModel.bump (Float.ofInt bump)").length == 3 do
    throwError "the call is exposed to binder capture:\n{rendered}"

-- A binder named after the emitted vocabulary itself (`pure`) is primed,
-- keeping the annotation provable instead of capturing the leaf.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "f", params := nums #["x"], source := "f",
                            body := #[.ret (.id "x")] }]
    obligations := #[{ function := "f", property := "p", formula := "f",
                       payload := .structured #[.int "pure"] #[]
                         (.istrue (.binop ">=" (.call "f" none #[.id "pure"])
                                             (.num "0"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "pure'").length == 3 do
    throwError "the reserved binder name is not primed:\n{rendered}"

-- A mutable local renders as `let mut`, a reassigned parameter is rebound
-- ahead of the body, and no join helper reaches the source text.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "clampUp", params := nums #["x"], source := "clampUp",
                            body := #[
                              .ite (.binop "<" (.id "x") (.num "1"))
                                #[.assign "x" (.num "1")] none,
                              .ret (.id "x")] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "let mut x := x").length == 2 do
    throwError "the assigned parameter is not rebound:\n{rendered}"
  unless (rendered.splitOn "fun").length == 1 do
    throwError "a helper lambda leaked into the source text:\n{rendered}"

-- Pure arms render as one `if`, both in place: no lift barrier, since a
-- pure arm has nothing to fire.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "canon", params := nums #["x"], source := "canon",
                            body := #[.ret (.cond (.binop "<" (.id "x") (.num "1"))
                                                  (.num "0") (.id "x"))] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "if Float.lt x 1 then 0 else x").length == 2 do
    throwError "the conditional did not render as a plain if:\n{rendered}"
  unless (rendered.splitOn "JsM _").length == 1 do
    throwError "pure arms took the lift barrier:\n{rendered}"

-- A lifting arm renders behind a nested `do`, so a throwing call in the
-- arm the condition did not take never fires.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "g", params := nums #["x"], source := "g",
                            body := #[.ret (.id "x")] },
                      .fn { name := "pick", params := nums #["x"], source := "pick",
                            body := #[.ret (.cond (.binop "<" (.id "x") (.num "1"))
                                                  (.call "g" none #[.id "x"])
                                                  (.num "0"))] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "JsM _").length == 3 do
    throwError "a lifting arm did not take the lift barrier:\n{rendered}"
  -- Only the ascription's presence distinguishes the two renderings: drop
  -- it and the text still reads as if the call sat in the arm, but the
  -- `←` no longer elaborates there at all.

-- What that shape buys, written out by hand: the arm the condition passed
-- over does not run, so its throw does not escape.
section
open Js
private def boom : JsM JsNumber := JsM.throw (JsError.error "E")

private def barrier (c : Bool) : JsM JsNumber := do
  return (← if c then ((do return 1) : JsM _) else ((do return (← boom)) : JsM _))

#guard (barrier true) matches .ok _
#guard (barrier false) matches .error _
end

-- A shape outside the slice is refused with a message naming the gap.
-- Module qualification travels in the `module` field; a joined spelling
-- in `name` is not a second way in.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "helper.mts::double", params := nums #["x"],
                            source := "f", body := #[.ret (.id "x")] }]
    obligations := #[] }
  let refused ← try
    let _ ← renderEmission e
    pure false
  catch _ => pure true
  unless refused do
    throwError "a joined module-qualified name was rendered instead of refused"

-- A module path that would break its own name component is refused, not
-- approximated: the artifact is re-parsed text.
#eval show CoreM Unit from do
  for bad in ["a«b", "/abs.ts", ""] do
    let e : Emission := {
      file := "t.ts"
      declarations := #[.fn { name := "double", module := some bad, params := nums #["x"],
                              source := "f", body := #[.ret (.id "x")] }]
      obligations := #[] }
    let refused ← try
      let _ ← renderEmission e
      pure false
    catch _ => pure true
    unless refused do
      throwError s!"module path '{bad}' was rendered instead of refused"

-- `Object.is` is a pure Bool application: no `←` on the call itself,
-- and an Int-binder argument still crosses to Float.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "canon", params := nums #["x"], source := "canon",
                            body := #[
                              .ite (.sameValue (.id "x") (.num "-0"))
                                #[.ret (.num "0")] none,
                              .ret (.id "x")] }]
    obligations := #[{ function := "canon", property := "p", formula := "f",
                       payload := .structured #[.range "n" 0 2]
                         #[.sameValue (.id "n") (.num "1")]
                         (.istrue (.binop "===" (.call "canon" none #[.id "n"]) (.num "1"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "if Number.FloatOps.sameValue x (-0) then").length == 2 do
    throwError "the branch condition did not render as sameValue:\n{rendered}"
  unless (rendered.splitOn "Number.FloatOps.sameValue (Float.ofInt n) 1").length == 2 do
    throwError "the guard argument was not coerced:\n{rendered}"

-- The renderer spells NaN and Infinity as the Js library's
-- kernel-reducible constants. A parameter spelled like the NaN constant
-- is primed out of its way.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[
      .fn { name := "addNaN", params := nums #["x"], source := "addNaN",
            body := #[.ret (.binop "+" (.id "x") (.num "NaN"))] },
      .fn { name := "shadow", params := nums #["floatNaN"], source := "shadow",
            body := #[.ret (.id "floatNaN")] }]
    obligations := #[{ function := "addNaN", property := "p", formula := "f",
                       payload := .structured #[.range "n" 0 2] #[]
                         (.istrue (.binop "<" (.call "addNaN" none #[.id "n"])
                           (.num "Infinity"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "x + floatNaN").length == 2 do
    throwError "NaN did not render as floatNaN:\n{rendered}"
  unless (rendered.splitOn "floatNaN'").length == 3 do
    throwError "the parameter spelled floatNaN was not primed:\n{rendered}"
  unless (rendered.splitOn "floatInf").length == 2 do
    throwError "Infinity did not render as floatInf in a comparison:\n{rendered}"

-- `Math.sqrt` is a pure application: no `←` of its own, and an
-- Int-binder argument still crosses to Float.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "root", params := nums #["x"], source := "root",
                            body := #[.ret (.mathSqrt (.id "x"))] }]
    obligations := #[{ function := "root", property := "p", formula := "f",
                       payload := .structured #[.range "n" 0 2] #[]
                         (.istrue (.binop ">="
                           (.mathSqrt (.id "n")) (.num "0"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "Float.sqrt x").length == 2 do
    throwError "the body did not render as Float.sqrt:\n{rendered}"
  unless (rendered.splitOn "Float.sqrt (Float.ofInt n)").length == 2 do
    throwError "the formula argument was not coerced:\n{rendered}"

-- Pure logical operands render as the Bool operators; a lifted right
-- operand renders behind the choice, so its effects never hoist past it.
#eval show CoreM Unit from do
  let cmp (n : String) (lit : String) : JsExpr := .binop "===" (.id n) (.num lit)
  let e : Emission := {
    file := "t.ts"
    declarations := #[
      .fn { name := "boom", params := nums #["x"], source := "boom",
            body := #[.throwErr "RangeError"] },
      .fn { name := "pick", params := nums #["x"], source := "pick",
            body := #[
              .ite (.binop "||" (cmp "x" "0") (cmp "x" "1")) #[.ret (.num "0")] none,
              .ite (.binop "||" (cmp "x" "2")
                     (.binop "===" (.call "boom" none #[.id "x"]) (.num "0")))
                #[.ret (.num "0")] none,
              .ite (.binop "&&" (cmp "x" "3")
                     (.binop "===" (.call "boom" none #[.id "x"]) (.num "0")))
                #[.ret (.num "0")] none,
              .ite (.unop "!" (.sameValue (.id "x") (.num "NaN")))
                #[.ret (.num "0")] none,
              .ret (.num "1")] }]
    obligations := #[] }
  let rendered ← renderEmission e
  -- Where the printer breaks a long term is its own business; where the
  -- lift sits relative to the choice is not, so the checks read one line.
  let flat := rendered.foldl
    (fun acc c =>
      if c.isWhitespace then (if acc.endsWith " " then acc else acc.push ' ')
      else acc.push c) ""
  unless (flat.splitOn "(Float.beq x 0 || Float.beq x 1)").length == 2 do
    throwError "pure || did not render as Bool.or:\n{rendered}"
  unless (flat.splitOn ("(← if Float.beq x 2 then pure true else " ++
      "((do return Float.beq (← TsModel.boom x) 0) : JsM Bool))")).length == 2 do
    throwError "a lifted right || operand did not render behind the choice:\n{rendered}"
  unless (flat.splitOn ("(← if Float.beq x 3 then " ++
      "((do return Float.beq (← TsModel.boom x) 0) : JsM Bool) else pure false)")).length == 2 do
    throwError "a lifted right && operand did not render behind the choice:\n{rendered}"
  unless (flat.splitOn "(!Number.FloatOps.sameValue x floatNaN)").length == 2 do
    throwError "! did not render as Bool.not:\n{rendered}"

-- A method is a function of the instance and its parameters, rendered
-- after the getters so an earlier method resolves for a later body.
#eval show CoreM Unit from do
  let box : EmitClass := {
    name := "Box", source := "class Box"
    fields := #["#v"], ctorParams := nums #["v"]
    ctorBody := #[.fieldSet "#v" (.id "v")]
    getters := #[]
    methods := #[
      { name := "base", params := #[]
        body := #[.ret (.fieldRead "Box" none "#v" .selfRef)] },
      { name := "scale", params := nums #["k"]
        body := #[.ret (.binop "*"
          (.methodCall "Box" none "base" .selfRef #[]) (.id "k"))] }] }
  let e : Emission := { file := "t.ts", declarations := #[.cls box], obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "def TsModel.Box.base (self : TsModel.Box) : JsM JsNumber := do").length == 2 do
    throwError "the zero-parameter method def is missing:\n{rendered}"
  unless (rendered.splitOn "def TsModel.Box.scale (self : TsModel.Box) (k : JsNumber) : JsM JsNumber := do").length == 2 do
    throwError "the parameterized method def is missing:\n{rendered}"
  unless (rendered.splitOn "← TsModel.Box.base self").length == 2 do
    throwError "the this-call is not applied to self:\n{rendered}"

-- A method call on a fresh instance lifts receiver-first.
#eval show CoreM Unit from do
  let box : EmitClass := {
    name := "Box", source := "class Box"
    fields := #["#v"], ctorParams := nums #["v"]
    ctorBody := #[.fieldSet "#v" (.id "v")]
    getters := #[]
    methods := #[{ name := "double", params := #[]
                   body := #[.ret (.binop "*"
                     (.fieldRead "Box" none "#v" .selfRef) (.num "2"))] }] }
  let e : Emission := {
    file := "t.ts", declarations := #[.cls box]
    obligations := #[{ function := "Box#double", property := "doubled"
                       formula := "forall (x: number) { … }"
                       payload := .structured #[.number "x" none none] #[]
                         (.eq (.methodCall "Box" none "double"
                             (.newObj "Box" none #[.id "x"]) #[])
                           (.binop "*" (.id "x") (.num "2"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "← TsModel.Box.double (← TsModel.Box.construct x)").length == 2 do
    throwError "the instance method call did not render:\n{rendered}"

-- A class binder quantifies over the constructor's image: one ungrouped ∀
-- per synthesized argument, then the instance, then the hypothesis naming
-- it as the constructor's output. The `-0` normalization and every guard
-- are inside the domain by construction, since `p` is what `construct`
-- returned rather than a bare `mk` of the arguments.
#eval show CoreM Unit from do
  let point : EmitClass := {
    name := "Point", source := "class Point"
    fields := #["x"], ctorParams := nums #["x"]
    ctorBody := #[.fieldSet "x" (.id "x")]
    getters := #[]
    methods := #[{ name := "gap", params := nums #["q"]
                   body := #[.ret (.fieldRead "Point" none "x" .selfRef)] }] }
  let e : Emission := {
    file := "t.ts", declarations := #[.cls point]
    obligations := #[{ function := "Point#gap", property := "nn"
                       formula := "forall (p: Point) { … }"
                       payload := .structured
                         #[.cls "p" "Point" none #[.number "x" false]]
                         #[] (.istrue (.binop "<="
                           (.num "0")
                           (.methodCall "Point" none "gap" (.id "p")
                             #[.num "1"]))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "∀ («p.x» : JsNumber),").length == 2 do
    throwError "the synthesized constructor argument is not its own ∀:\n{rendered}"
  let underArg := rendered.splitOn "∀ («p.x» : JsNumber),"
  unless ((underArg[1]!).splitOn "∀ (p : TsModel.Point),").length == 2 do
    throwError "the instance ∀ is not inside its arguments:\n{rendered}"
  unless (rendered.splitOn "TsModel.Point.construct «p.x» = .ok p →").length == 2 do
    throwError "the constructor-image hypothesis did not render:\n{rendered}"
  unless (rendered.splitOn "Float.ofInt").length == 1 do
    throwError "a class binder was coerced from Int:\n{rendered}"

/-- The union signature most union fixtures share. -/
def unionParam (n : String) : Param :=
  { name := n, ty := .union #[.number, .string] }

-- A union-typed parameter renders as `(v : JsVal)` — one Lean type for
-- every union spelling — with the typeof dispatch, the throwing
-- projection behind `←`, and the injected obligation argument.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn
      { name := "toNum", params := #[unionParam "v"], source := "toNum",
        body := #[
          .ite (.typeofTest (.id "v") "number")
            #[.ret (.project .number (.id "v"))] none,
          .ret (.num "0")] }]
    obligations := #[
      { function := "toNum", property := "numId", formula := "f",
        payload := .structured #[.number "x" none none] #[]
          (.eq (.call "toNum" none #[.inject .number (some (.id "x"))])
               (.id "x")) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "def TsModel.toNum (v : JsVal) : JsM JsNumber := do").length == 2 do
    throwError "the union parameter is not a JsVal binder:\n{rendered}"
  unless (rendered.splitOn "if JsVal.typeof v == TypeofResult.number then").length == 2 do
    throwError "the typeof test did not render:\n{rendered}"
  unless (rendered.splitOn "return (← JsVal.toNumber v)").length == 2 do
    throwError "the projection is not behind ←:\n{rendered}"
  unless (rendered.splitOn "TsModel.toNum (JsVal.num x)").length == 2 do
    throwError "the obligation argument is not injected:\n{rendered}"

-- An Int-binder argument injects through its Float coercion, and both
-- JsVal equalities render as the pure Bool predicates.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn
      { name := "nullFlag",
        params := #[{ name := "v", ty := .union #[.number, .null] }],
        source := "nullFlag",
        body := #[
          .ite (.jsvalEq true (.id "v") (.inject .null none))
            #[.ret (.num "1")] none,
          .ret (.num "0")] }]
    obligations := #[
      { function := "nullFlag", property := "p", formula := "f",
        payload := .structured #[.range "n" 0 4] #[]
          (.eq (.call "nullFlag" none #[.inject .number (some (.id "n"))])
               (.num "0")) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "if JsVal.sameValue v JsVal.null then").length == 2 do
    throwError "same-value over JsVal did not render:\n{rendered}"
  unless (rendered.splitOn "JsVal.num (Float.ofInt n)").length == 2 do
    throwError "the coerced binder argument is not injected:\n{rendered}"

-- strictEq spells `===` over unions; a parameter spelled like the new
-- vocabulary is primed out of its way.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "t.ts"
    declarations := #[
      .fn
        { name := "eq", params := #[unionParam "v", unionParam "w"],
          source := "eq",
          body := #[
            .ite (.jsvalEq false (.id "v") (.id "w"))
              #[.ret (.num "1")] none,
            .ret (.num "0")] },
      .fn
        { name := "shadow", params := #[{ name := "JsVal", ty := .number }],
          source := "shadow", body := #[.ret (.id "JsVal")] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "if JsVal.strictEq v w then").length == 2 do
    throwError "strictEq over JsVal did not render:\n{rendered}"
  unless (rendered.splitOn "JsVal'").length == 3 do
    throwError "the JsVal-spelled parameter was not primed:\n{rendered}"
