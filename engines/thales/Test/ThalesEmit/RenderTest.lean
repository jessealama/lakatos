import Test.ThalesEmit.Support

/-! One guard per rendering rule: the tree the renderer builds against the
tree a person would write, no pretty-printer in the loop. -/

open Lean ThalesEmit

def nums (names : Array String) : Array Param :=
  names.map fun n => { name := n, ty := .number }

def v (e : JsExpr) : RenderM Rendered := valueTerm (fun _ => false) e
/-- With `x` an Int-valued binder. -/
def vx (e : JsExpr) : RenderM Rendered := valueTerm (· == "x") e
def call1 (f x : String) : JsExpr := .call f none #[.id x]

-- Literals: decimal and scientific print as themselves, the two
-- non-finite spellings as the Js library's constants, a sign as negation.
#guard rendersAs (v (.num "3")) `(3)
#guard rendersAs (v (.num "1.5")) `(1.5)
#guard rendersAs (v (.num "1e3")) `(1e3)
#guard rendersAs (v (.num "-2")) `(-2)
#guard rendersAs (v (.num "Infinity")) `(floatInf)
#guard rendersAs (v (.num "-Infinity")) `(-floatInf)
#guard rendersAs (v (.num "NaN")) `(floatNaN)

-- Identifiers: an Int binder crosses to Float at each use; a reserved
-- spelling is primed; a non-identifier is refused.
#guard rendersAs (v (.id "x")) `(x)
#guard rendersAs (vx (.id "x")) `(Float.ofInt x)
#guard rendersAs (vx (.id "y")) `(y)
#guard rendersAs (v (.id "pure")) `(pure')
#guard rendersAs (v (.id "floatNaN")) `(floatNaN')
#guard renderFails (v (.id ""))
#guard renderFails (v (.id "a-b"))

-- Unary: minus negates, plus is the identity, bang is Bool.not.
#guard rendersAs (v (.unop "-" (.id "x"))) `(-x)
#guard rendersAs (v (.unop "+" (.id "x"))) `(x)
#guard rendersAs (v (.unop "!" (.id "b"))) `(!b)
#guard renderFails (v (.unop "~" (.id "x")))

-- Arithmetic and comparison. `>`/`>=` flip into the IEEE predicates.
#guard rendersAs (v (.binop "+" (.id "x") (.id "y"))) `(x + y)
#guard rendersAs (v (.binop "-" (.id "x") (.id "y"))) `(x - y)
#guard rendersAs (v (.binop "*" (.id "x") (.id "y"))) `(x * y)
#guard rendersAs (v (.binop "/" (.id "x") (.id "y"))) `(x / y)
#guard rendersAs (v (.binop "%" (.id "x") (.id "y"))) `(Number.FloatOps.tsRem x y)
#guard rendersAs (v (.binop "<" (.id "x") (.id "y"))) `(Float.lt x y)
#guard rendersAs (v (.binop "<=" (.id "x") (.id "y"))) `(Float.le x y)
#guard rendersAs (v (.binop ">" (.id "x") (.id "y"))) `(Float.lt y x)
#guard rendersAs (v (.binop ">=" (.id "x") (.id "y"))) `(Float.le y x)
#guard rendersAs (v (.binop "===" (.id "x") (.id "y"))) `(Float.beq x y)
#guard rendersAs (v (.binop "!==" (.id "x") (.id "y"))) `(!Float.beq x y)
#guard renderFails (v (.binop "**" (.id "x") (.id "y")))
-- A flip with one lift keeps the lift where it is; with two, a lambda
-- keeps the lifts in JS evaluation order.
#guard rendersLifted (v (.binop ">" (call1 "f" "x") (.id "y"))) true
  `(Float.lt y (← TsModel.f x))
#guard rendersLifted (v (.binop ">=" (call1 "f" "x") (call1 "g" "y"))) true
  `((fun a b => Float.le b a) (← TsModel.f x) (← TsModel.g y))
#guard rendersLifted (v (.binop "+" (call1 "f" "x") (.num "1"))) true
  `((← TsModel.f x) + 1)

-- Logical: pure operands are the Bool operators; a lifted right operand
-- renders behind the choice, ascribed, so its effects never hoist.
#guard rendersLifted (v (.binop "||" (.id "a") (.id "b"))) false `(a || b)
#guard rendersLifted (v (.binop "&&" (.id "a") (.id "b"))) false `(a && b)
#guard rendersLifted (v (.binop "||" (.id "a") (call1 "f" "x"))) true
  `((← if a then pure true else ((do return (← TsModel.f x)) : JsM Bool)))
#guard rendersLifted (v (.binop "&&" (.id "a") (call1 "f" "x"))) true
  `((← if a then ((do return (← TsModel.f x)) : JsM Bool) else pure false))
#guard rendersLifted (v (.binop "||" (call1 "f" "x") (.id "b"))) true
  `((← TsModel.f x) || b)

-- SameValue, the conditional, and the builtin applications.
#guard rendersAs (v (.sameValue (.id "x") (.num "-0"))) `(Number.FloatOps.sameValue x (-0))
#guard rendersAs (vx (.sameValue (.id "x") (.num "1"))) `(Number.FloatOps.sameValue (Float.ofInt x) 1)
#guard rendersLifted (v (.cond (.id "c") (.num "0") (.id "x"))) false `(if c then 0 else x)
#guard rendersLifted (v (.cond (call1 "f" "c") (.num "0") (.id "x"))) true
  `(if (← TsModel.f c) then 0 else x)
#guard rendersLifted (v (.cond (.id "c") (call1 "f" "x") (.num "0"))) true
  `((← if c then ((do return (← TsModel.f x)) : JsM _) else ((do return 0) : JsM _)))
#guard rendersAs (v (.mathSqrt (.id "x"))) `(Float.sqrt x)
#guard rendersAs (vx (.mathSqrt (.id "x"))) `(Float.sqrt (Float.ofInt x))
#guard rendersAs (v (.mathAbs (.id "x"))) `(Float.abs x)
#guard rendersAs (v (.numberIsFinite (.id "x"))) `(Float.isFinite x)
#guard rendersAs (v (.numberIsNaN (.id "x"))) `(Float.isNaN x)

-- Calls lift, under the model namespace, a dependency's one component
-- deeper; a binder named after the callee cannot capture it.
#guard rendersLifted (v (.call "f" none #[])) true `((← TsModel.f))
#guard rendersLifted (v (.call "f" none #[.id "x", .id "y"])) true `((← TsModel.f x y))
#guard rendersLifted (v (.call "f" (some "helper.mts") #[.id "x"])) true
  `((← TsModel.«helper.mts».f x))
#guard rendersAs (v (.call "bump" none #[.id "bump"])) `((← TsModel.bump bump))
#guard rendersAs (vx (.call "f" none #[.id "x"])) `((← TsModel.f (Float.ofInt x)))
#guard renderFails (v (.call "helper.mts::double" none #[]))

-- Classes: construction, getter, field, method, receiver.
#guard rendersLifted (v (.newObj "Box" none #[.id "x"])) true `((← TsModel.Box.construct x))
#guard rendersLifted (v (.newObj "Box" none #[])) true `((← TsModel.Box.construct))
#guard rendersLifted (v (.getterRead "Box" none "v" .selfRef)) true `((← TsModel.Box.v self))
#guard rendersLifted (v (.fieldRead "Box" none "#v" .selfRef)) false `(TsModel.Box.«#v» self)
#guard rendersLifted (v (.fieldRead "Box" none "v" (.newObj "Box" none #[.id "x"]))) true
  `(TsModel.Box.v (← TsModel.Box.construct x))
#guard rendersLifted (v (.methodCall "Box" none "m" (.id "b") #[.id "k"])) true
  `((← TsModel.Box.m b k))
#guard rendersLifted (v (.methodCall "Box" none "double" (.newObj "Box" none #[.id "x"]) #[])) true
  `((← TsModel.Box.double (← TsModel.Box.construct x)))
#guard rendersAs (v .selfRef) `(self)
#guard rendersAs (v (.fieldRead "Box" (some "b.mts") "v" .selfRef)) `(TsModel.«b.mts».Box.v self)

-- Module constants read as qualified references.
#guard rendersLifted (v (.constRead "cap" none)) false `(TsModel.cap)
#guard rendersAs (v (.constRead "cap" (some "c.mts"))) `(TsModel.«c.mts».cap)

-- The tagged domain: injection by constructor, the throwing projection
-- behind a bind, typeof as a TypeofResult comparison, both equalities.
#guard rendersLifted (v (.inject .number (some (.id "x")))) false `(JsVal.num x)
#guard rendersAs (vx (.inject .number (some (.id "x")))) `(JsVal.num (Float.ofInt x))
#guard rendersAs (v (.inject .boolean (some (.id "b")))) `(JsVal.bool b)
#guard rendersAs (v (.inject .undefined none)) `(JsVal.undef)
#guard rendersAs (v (.inject .null none)) `(JsVal.null)
#guard renderFails (v (.inject .string (some (.id "s"))))
#guard renderFails (v (.inject .number none))
#guard rendersLifted (v (.project .number (.id "w"))) true `((← JsVal.toNumber w))
#guard renderFails (v (.project .string (.id "w")))
#guard rendersAs (v (.typeofTest (.id "w") "number")) `(JsVal.typeof w == TypeofResult.number)
#guard renderFails (v (.typeofTest (.id "w") "numbr"))
#guard rendersAs (v (.jsvalEq true (.id "w") (.inject .null none))) `(JsVal.sameValue w JsVal.null)
#guard rendersAs (v (.jsvalEq false (.id "w") (.id "u"))) `(JsVal.strictEq w u)

-- Options: injection, the two tests, the throwing get.
#guard rendersLifted (v (.optionInject (some (.id "q")))) false `(some q)
#guard rendersAs (v (.optionInject none)) `(none)
#guard rendersAs (v (.optionTest (.id "p") true)) `(Option.isSome p)
#guard rendersAs (v (.optionTest (.id "p") false)) `(Option.isNone p)
#guard rendersLifted (v (.optionGet (.id "p"))) true `((← Js.optionGet p))

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

-- What the lift barrier buys, written out by hand: the arm the condition
-- passed over does not run, so its throw does not escape.
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
