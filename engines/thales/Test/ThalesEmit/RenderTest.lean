import ThalesEmit

open Lean ThalesEmit

/-- Number-typed parameters, the signature most of these fixtures have. -/
def nums (names : Array String) : Array Param :=
  names.map fun n => { name := n, ty := .number }

/-- A number parameter as the wire spells it. -/
def numParamJson (name : String) : Json :=
  Json.mkObj [("name", name), ("type", "number")]

-- Schema violations decode to errors naming the offender, never to
-- defaults.
#guard (decodeEmission (Json.mkObj [])) matches .error _
#guard
  (decodeEmission (Json.mkObj
    [("file", "t.ts"), ("declarations", Json.arr #[Json.mkObj [("kind", "enum")]]),
     ("obligations", Json.arr #[])]))
  matches .error "unknown declaration kind 'enum'"
-- A known kind is still decoded strictly: a class missing its name is a
-- field error, not a default.
#guard
  (decodeEmission (Json.mkObj
    [("file", "t.ts"), ("declarations", Json.arr #[Json.mkObj [("kind", "class")]]),
     ("obligations", Json.arr #[])]))
  matches .error "property not found: name"

-- The unary-operator and binder-domain IR decodes strictly.
#guard
  (decodeExpr (Json.mkObj
    [("kind", "unop"), ("op", "-"), ("operand", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.unop "-" (.id "x"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "same-value"),
     ("left", Json.mkObj [("kind", "id"), ("name", "x")]),
     ("right", Json.mkObj [("kind", "num"), ("lit", "-0")])]))
  matches .ok (.sameValue (.id "x") (.num "-0"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "cond"),
     ("cond", Json.mkObj [("kind", "id"), ("name", "b")]),
     ("then", Json.mkObj [("kind", "num"), ("lit", "0")]),
     ("else", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.cond (.id "b") (.num "0") (.id "x"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "math-sqrt"),
     ("arg", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.mathSqrt (.id "x"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "math-abs"),
     ("arg", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.mathAbs (.id "x"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "number-is-finite"),
     ("arg", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.numberIsFinite (.id "x"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "number-is-nan"),
     ("arg", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.numberIsNaN (.id "x"))
-- The class IR: instance construction, member reads, the receiver, and
-- a constructor's field assignment.
#guard
  (decodeExpr (Json.mkObj
    [("kind", "new"), ("className", "Box"),
     ("args", Json.arr #[Json.mkObj [("kind", "id"), ("name", "x")]])]))
  matches .ok (.newObj "Box" none #[.id "x"])
#guard
  (decodeExpr (Json.mkObj
    [("kind", "getter-read"), ("className", "Box"), ("name", "v"),
     ("object", Json.mkObj [("kind", "self")])]))
  matches .ok (.getterRead "Box" none "v" .selfRef)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "field-read"), ("className", "Box"), ("field", "#v"),
     ("object", Json.mkObj [("kind", "self")])]))
  matches .ok (.fieldRead "Box" none "#v" .selfRef)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "method-call"), ("className", "Box"), ("name", "double"),
     ("object", Json.mkObj [("kind", "self")]),
     ("args", Json.arr #[Json.mkObj [("kind", "id"), ("name", "y")]])]))
  matches .ok (.methodCall "Box" none "double" .selfRef #[.id "y"])
#guard
  (decodeStmt (Json.mkObj
    [("kind", "field-set"), ("field", "#v"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "v")])]))
  matches .ok (.fieldSet "#v" (.id "v"))
#guard
  (decodeDecl (Json.mkObj
    [("kind", "class"), ("name", "Box"), ("source", "class Box {}"),
     ("fields", Json.arr #["#v"]),
     ("ctor", Json.mkObj
       [("params", Json.arr #[numParamJson "v"]),
        ("body", Json.arr #[Json.mkObj
          [("kind", "field-set"), ("field", "#v"),
           ("expr", Json.mkObj [("kind", "id"), ("name", "v")])]])]),
     ("getters", Json.arr #[Json.mkObj
       [("name", "v"),
        ("body", Json.arr #[Json.mkObj
          [("kind", "return"),
           ("expr", Json.mkObj
             [("kind", "field-read"), ("className", "Box"), ("field", "#v"),
              ("object", Json.mkObj [("kind", "self")])])]])]]),
     ("methods", Json.arr #[Json.mkObj
       [("name", "scale"), ("params", Json.arr #[numParamJson "k"]),
        ("body", Json.arr #[Json.mkObj
          [("kind", "return"),
           ("expr", Json.mkObj [("kind", "id"), ("name", "k")])]])]])]))
  matches .ok (.cls { methods := #[{ name := "scale", .. }], .. })
-- A parameter's type is "number" or a class object; anything else fails
-- the run rather than defaulting to a number.
#guard (decodeParam (numParamJson "x")) matches .ok { name := "x", ty := .number }
#guard
  (decodeParam (Json.mkObj
    [("name", "p"), ("type", Json.mkObj [("class", "Point")])]))
  matches .ok { name := "p", ty := .cls "Point" none }
#guard
  (decodeParam (Json.mkObj
    [("name", "p"),
     ("type", Json.mkObj [("class", "Point"), ("module", "point.mts")])]))
  matches .ok { name := "p", ty := .cls "Point" (some "point.mts") }
#guard
  (decodeParam (Json.mkObj [("name", "s"), ("type", "string")]))
  matches .error "unknown parameter type 'string'"
#guard
  (decodeParams (Json.mkObj [("params", Json.arr #[Json.mkObj [("name", "x")]])])
    "params")
  matches .error "field 'params': property not found: type"
-- A method missing its params is a field error, not a default.
#guard
  (decodeClass (Json.mkObj
    [("kind", "class"), ("name", "Box"), ("source", "class Box {}"),
     ("fields", Json.arr #[]), ("getters", Json.arr #[]),
     ("ctor", Json.mkObj [("params", Json.arr #[]), ("body", Json.arr #[])]),
     ("methods", Json.arr #[Json.mkObj [("name", "m")]])]))
  matches .error "property not found: params"
-- A class without its constructor is a decode error, never a default.
#guard
  (decodeDecl (Json.mkObj
    [("kind", "class"), ("name", "Box"), ("source", "class Box {}"),
     ("fields", Json.arr #[]), ("getters", Json.arr #[])]))
  matches .error _

#guard
  (decodeBinder (Json.mkObj [("name", "x"), ("kind", "int")]))
  matches .ok (.int "x")
#guard
  (decodeBinder (Json.mkObj [("name", "n"), ("kind", "nat")]))
  matches .ok (.nat "n")
#guard
  (decodeBinder (Json.mkObj
    [("name", "x"), ("kind", "range"), ("lo", "0"), ("hi", "10")]))
  matches .ok (.range "x" 0 10)
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"),
     ("lower", Json.mkObj [("op", "<"), ("lit", "0")]),
     ("upper", Json.mkObj [("op", "<="), ("lit", "1")])]))
  matches .ok (.number "a" (some ("<", "0")) (some ("<=", "1")))
-- An absent side is a missing field, so a rangeless binder decodes bare.
#guard
  (decodeBinder (Json.mkObj [("name", "a"), ("kind", "number")]))
  matches .ok (.number "a" none none)
-- A class binder carries the class it ranges over and its constructor's
-- parameter spellings; the module qualifier is absent for the entry's own.
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point"),
     ("ctorParams", Json.arr #["x", "y"])]))
  matches .ok (.cls "p" "Point" none #["x", "y"])
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point"),
     ("module", "dep.ts"), ("ctorParams", Json.arr #[])]))
  matches .ok (.cls "p" "Point" (some "dep.ts") #[])
-- The parameter spellings are strings, and a missing list fails the run.
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point"),
     ("ctorParams", Json.arr #[(1 : Nat)])]))
  matches .error _
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point")]))
  matches .error _
#guard (decodeBinder (Json.mkObj [("name", "x"), ("kind", "real")])) matches .error _
-- A bound is an op × literal pair; a bare string is not one.
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"), ("lower", "0")]))
  matches .error _

-- Guards are optional, decode in order, and name their own field when
-- they break the schema.
def payloadShell (guards : Json) : Json :=
  Json.mkObj
    [("kind", "structured"), ("binders", Json.arr #[]), ("guards", guards),
     ("conclusion", Json.mkObj
       [("kind", "istrue"), ("expr", Json.mkObj [("kind", "id"), ("name", "b")])])]

#guard
  (decodePayload (payloadShell (Json.arr
    #[Json.mkObj [("kind", "id"), ("name", "g")],
      Json.mkObj [("kind", "id"), ("name", "h")]])))
  matches .ok (.structured #[] #[.id "g", .id "h"] (.istrue (.id "b")))
#guard (decodePayload (payloadShell "g")) matches .error "field 'guards' is not an array"
#guard
  (decodePayload (payloadShell (Json.arr #[Json.mkObj [("kind", "typeof")]])))
  matches .error "field 'guards': unknown expression kind 'typeof'"

-- The pinned emissions render to the golden artifacts — files a human
-- inspected and accepted. #eval runs CoreM inside this module's own
-- environment, which imports ThalesDsl transitively, so the printer has
-- its syntax tables. Paths are relative to engines/thales, where every
-- lake invocation runs.
def goldenCheck (emissionPath expectedPath : String) : CoreM Unit := do
  let text ← IO.FS.readFile emissionPath
  let json ← IO.ofExcept (Json.parse text)
  let e ← IO.ofExcept (decodeEmission json)
  let rendered ← renderEmission e
  let expected ← IO.FS.readFile expectedPath
  unless rendered == expected do
    throwError "rendered artifact drifted from the golden file:\n{rendered}"

#eval goldenCheck "tests/fixtures/tracer.emission.json"
  "tests/fixtures/tracer.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/operators.emission.json"
  "tests/fixtures/operators.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/statements.emission.json"
  "tests/fixtures/statements.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/binders.emission.json"
  "tests/fixtures/binders.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/degradations.emission.json"
  "tests/fixtures/degradations.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/classes.emission.json"
  "tests/fixtures/classes.emitted.lean.expected"

#eval goldenCheck "tests/fixtures/class-params.emission.json"
  "tests/fixtures/class-params.emitted.lean.expected"

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

-- The statement decoding round-trips strictly, else arm optional.
#guard
  (decodeStmt (Json.mkObj [("kind", "throw"), ("error", "RangeError")]))
  matches .ok (.throwErr "RangeError")
#guard
  (decodeStmt (Json.mkObj
    [("kind", "let"), ("name", "y"),
     ("init", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.letDecl "y" (.id "x"))
#guard
  (decodeStmt (Json.mkObj
    [("kind", "if"),
     ("cond", Json.mkObj [("kind", "id"), ("name", "b")]),
     ("then", Json.arr #[Json.mkObj [("kind", "throw"), ("error", "E")]])]))
  matches .ok (.ite (.id "b") #[.throwErr "E"] none)
#guard (decodeStmt (Json.mkObj [("kind", "while")])) matches .error _

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

-- A number binder is a Float ∀ carrying its bounds as hypotheses, lower
-- outermost, with an infinite endpoint spelled `floatInf` — and no use of
-- it is coerced, since it is already a double. The wide conclusion also
-- pins the join: `return` never ends a line, which would read back as a
-- bare return.
#eval show CoreM Unit from do
  let call (x : String) : JsExpr :=
    .call "applyConversionFactors" none #[.id x, .id x, .id x, .id x, .id x]
  let e : Emission := {
    file := "t.ts"
    declarations := #[.fn { name := "applyConversionFactors",
                            params := nums #["v", "sf", "so", "tf", "to"],
                            source := "applyConversionFactors",
                            body := #[.ret (.id "v")] }]
    obligations := #[{ function := "applyConversionFactors", property := "p",
                       formula := "f",
                       payload := .structured
                         #[.number "x" (some ("<", "0")) (some ("<", "Infinity")),
                           .number "y" (some ("<=", "-Infinity")) none]
                         #[] (.istrue (.binop "<=" (call "x") (call "y"))) }] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "∀ (x : JsNumber),").length == 2 do
    throwError "the number binder is not a JsNumber ∀:\n{rendered}"
  -- The printer breaks after every arrow, so order is pinned by nesting:
  -- the upper bound must sit inside the lower.
  let underLower := rendered.splitOn "0 < x →"
  unless underLower.length == 2 do
    throwError "the lower bound did not render:\n{rendered}"
  unless ((underLower[1]!).splitOn "x < floatInf →").length == 2 do
    throwError "the upper bound is not inside the lower:\n{rendered}"
  unless (rendered.splitOn "-floatInf ≤ y →").length == 2 do
    throwError "the half-bounded number binder did not render:\n{rendered}"
  unless (rendered.splitOn "Float.ofInt").length == 1 do
    throwError "a number binder was coerced from Int:\n{rendered}"
  unless (rendered.splitOn "return\n").length == 1 do
    throwError "a return was split from its argument:\n{rendered}"
  -- The positive half of the same pin: the conclusion is wide enough that
  -- the printer breaks it, so this is the rejoined line, not an unbroken one.
  unless (rendered.splitOn "return Float.le").length == 2 do
    throwError "the return and its argument are not on one line:\n{rendered}"

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

-- A dependency's models carry their module as a name component; the
-- entry's own stay bare.
#eval show CoreM Unit from do
  let e : Emission := {
    file := "main.mts"
    declarations := #[
      .fn { name := "double", module := some "helper.mts", params := nums #["x"],
            source := "double", body := #[.ret (.binop "*" (.id "x") (.num "2"))] },
      .fn { name := "twice", params := nums #["x"], source := "twice",
            body := #[.ret (.call "double" (some "helper.mts") #[.id "x"])] }]
    obligations := #[] }
  let rendered ← renderEmission e
  unless (rendered.splitOn "def TsModel.«helper.mts».double").length == 2 do
    throwError "the dependency's def is not module-qualified:\n{rendered}"
  unless (rendered.splitOn "def TsModel.twice").length == 2 do
    throwError "the entry's def did not stay bare:\n{rendered}"
  unless (rendered.splitOn "TsModel.«helper.mts».double x").length == 2 do
    throwError "the call site is not module-qualified:\n{rendered}"
  -- The dependency's block is introduced once, ahead of its def; the
  -- entry's declarations get no separator of their own.
  unless (rendered.splitOn "-- module helper.mts\n").length == 2 do
    throwError "the module separator is missing or repeated:\n{rendered}"
  let afterSep := (rendered.splitOn "-- module helper.mts\n")[1]!
  unless (afterSep.splitOn "def TsModel.«helper.mts».double").length == 2 do
    throwError "the module separator does not precede its def:\n{rendered}"
  unless (rendered.splitOn "-- module ").length == 2 do
    throwError "the entry's declarations got a separator:\n{rendered}"

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

-- NaN is a num lit like Infinity already is: no decoder change, and the
-- renderer spells both as the Js library's kernel-reducible constants. A
-- parameter spelled like the NaN constant is primed out of its way.
#guard (decodeExpr (Json.mkObj [("kind", "num"), ("lit", "NaN")])) matches .ok (.num "NaN")
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
                       payload := .structured #[.cls "p" "Point" none #["x"]]
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
