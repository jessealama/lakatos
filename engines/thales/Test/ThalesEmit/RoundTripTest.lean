import ThalesEmit

/-! What the emitter prints, `propSpine` must read back: the expected spine
is derived from the IR, and a printed payload that recovers anything else
is a mismatch the emitter refuses. -/

open Lean ThalesEmit ThalesDsl

def spineOf (bs : Array BinderIR) : List SpineBinder :=
  match RenderM.run (expectedSpine bs) with
  | .ok s => s
  | .error _ => []

-- The expected spine names binders the way the renderer spells them.
#guard spineOf #[.range "x" 0 10] == [.ranged "x" 0 10]
#guard spineOf #[.range "x" (-5) 5, .int "y"] == [.ranged "x" (-5) 5, .unbounded "y"]
#guard spineOf #[.number "a" none none, .int "y"] == [.unbounded "a", .unbounded "y"]
#guard spineOf #[.int "pure"] == [.unbounded "pure'"]
#guard spineOf #[.cls "p" "Point" none #[.number "x" false, .number "y" true]]
  == [.unbounded "«p.x»", .unbounded "«p.y»", .opaque "p"]
#guard spineOf #[.cls "s" "Span" none #[.cls "p" "Point" none #[.number "x" false] false]]
  == [.unbounded "«s.p.x»", .opaque "«s.p»", .opaque "s"]
#guard spineOf #[.cls "f" "Flag" none #[.bool "on" false]] == [.bool "«f.on»", .opaque "f"]

-- A binder whose own bounds print as implications is read past them,
-- so the binders under it are expected too.
#guard spineOf #[.nat "n", .int "y"] == [.unbounded "n", .unbounded "y"]
#guard spineOf #[.number "a" (some (.lt, "0")) none, .int "y"] == [.unbounded "a", .unbounded "y"]
#guard spineOf #[.number "a" none (some (.le, "1")), .int "y"] == [.unbounded "a", .unbounded "y"]

def mismatch (expected : List SpineBinder) (guards : Nat) (t : Unhygienic Term) : Option String :=
  spineMismatch? expected guards (Unhygienic.run t)

-- The shapes emission writes recover exactly.
#guard mismatch [.ranged "x" 0 5] 0 `(ballIco 0 5 fun x => (pure true : JsM Bool) = pure true) == none
#guard mismatch [.unbounded "n"] 0 `(∀ (n : Int), 0 ≤ n → (pure true : JsM Bool) = pure true) == none
#guard mismatch [.unbounded "x"] 1
  `(∀ (x : JsNumber), (pure b : JsM Bool) = pure true → (pure true : JsM Bool) = pure true) == none
#guard mismatch [.unbounded "«p.x»", .opaque "p"] 0
  `(∀ («p.x» : JsNumber), ∀ (p : TsModel.Point),
      TsModel.Point.construct «p.x» = .ok p → (pure true : JsM Bool) = pure true) == none

-- The bounds a binder prints are read past, and the guards under them
-- are counted.
#guard mismatch [.unbounded "x", .unbounded "y"] 1
  `(∀ (x : JsNumber), 0 < x → ∀ (y : Int),
      (pure b : JsM Bool) = pure true → (pure true : JsM Bool) = pure true) == none
#guard mismatch [.unbounded "x", .unbounded "y", .unbounded "sf"] 1
  `(∀ (x : JsNumber), ∀ (y : JsNumber), ∀ (sf : JsNumber), 0 < sf → sf < floatInf →
      (pure b : JsM Bool) = pure true → (pure true : JsM Bool) = pure true) == none
-- Drift below a bounded binder is named like drift anywhere else.
#guard (mismatch [.unbounded "x", .unbounded "y"] 1
  `(∀ (x : JsNumber), 0 < x → ∀ (y z : Int),
      (pure true : JsM Bool) = pure true)).getD "" |>.startsWith "binder 1"
#guard (mismatch [.unbounded "x", .unbounded "y"] 1
  `(∀ (x : JsNumber), 0 < x → ∀ (y : Int),
      (pure true : JsM Bool) = pure true)) matches some _

#guard spineOf #[.range "n" 0 3, .bool "b"] == [.ranged "n" 0 3, .bool "b"]
#guard mismatch [.ranged "n" 0 3, .bool "b"] 0
  `(ballIco 0 3 fun n => ∀ (b : Bool), (pure true : JsM Bool) = pure true) == none
-- A grouped Bool ∀ is drift like any other.
#guard (mismatch [.bool "a", .bool "b"] 0
  `(∀ (a b : Bool), (pure true : JsM Bool) = pure true)) matches some _

-- Drift is named: a grouped ∀ recovers no binders; a parenthesized
-- endpoint is fine but a parenthesized domain type is not; a guard count
-- is checked once the binders agree.
#guard (mismatch [.unbounded "x", .unbounded "y"] 0
  `(∀ (x y : Int), (pure true : JsM Bool) = pure true)) matches some _
#guard mismatch [.ranged "x" 0 5] 0 `(ballIco (0) (5) fun x => (pure true : JsM Bool) = pure true) == none
#guard (mismatch [.unbounded "x"] 0
  `(∀ (x : (Int)), (pure true : JsM Bool) = pure true)) matches some _
#guard (mismatch [.ranged "x" 0 5] 1
  `(ballIco 0 5 fun x => (pure true : JsM Bool) = pure true)) matches some _
#guard (mismatch [.ranged "x" 0 5] 0
  `(ballIco 0 6 fun x => (pure true : JsM Bool) = pure true)) matches some _
-- The message says where.
#guard (mismatch [.unbounded "x", .unbounded "y"] 0
  `(∀ (x y : Int), (pure true : JsM Bool) = pure true)).getD "" |>.startsWith "binder 0"

-- The check runs on printed text, in the emitter's environment.
def wideObligation : Obligation :=
  { function := "f", property := "p", formula := "",
    payload := .structured #[.range "x" 0 10] #[] (.eq (.call "f" none #[.id "x"]) (.id "x")) }

#eval show CoreM Unit from do
  checkRoundTrip wideObligation
    "#thales_prove \"t.ts\" \"f\" \"p\" :=\n  ballIco 0 10 fun x => TsModel.f (Float.ofInt x) = pure (Float.ofInt x)"

-- A spelling propSpine cannot read fails with the obligation named.
#eval show CoreM Unit from do
  let failed ← try
    checkRoundTrip { wideObligation with payload := .structured #[.int "x", .int "y"] #[] (.eq (.id "x") (.id "y")) }
      "#thales_prove \"t.ts\" \"f\" \"p\" :=\n  ∀ (x y : Int), (pure (Float.ofInt x) : JsM JsNumber) = pure (Float.ofInt y)"
    pure none
  catch ex => pure (some (← ex.toMessageData.toString))
  let some msg := failed | throwError "a grouped ∀ was accepted"
  unless (msg.splitOn "f/p").length == 2 do
    throwError "the failure does not name the obligation: {msg}"
  unless (msg.splitOn "binder 0").length == 2 do
    throwError "the failure does not name the divergence: {msg}"

-- Text that does not parse is the same kind of failure.
#eval show CoreM Unit from do
  let failed ← try
    checkRoundTrip wideObligation "#thales_prove \"t.ts\" \"f\" \"p\" := ballIco 0 10 fun x =>"
    pure false
  catch _ => pure true
  unless failed do throwError "unparsable text was accepted"

-- A bare payload has nothing to check.
#eval show CoreM Unit from do
  checkRoundTrip { wideObligation with payload := .bare } "#thales_prove \"t.ts\" \"f\" \"p\""

-- Through the whole pipeline: every fixture still renders (the check runs
-- inside renderEmission), and a renderer that printed a grouped ∀ would
-- not. The negative half is the unit test above; this is the wiring.
#eval show CoreM Unit from do
  let e : Emission := { file := "t.ts", declarations := #[], obligations := #[wideObligation] }
  let _ ← renderEmission e
