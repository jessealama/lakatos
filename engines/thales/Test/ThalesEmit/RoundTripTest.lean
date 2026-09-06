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
#guard spineOf #[.nat "n", .number "a" (some (.lt, "0")) none] == [.unbounded "n", .unbounded "a"]
#guard spineOf #[.int "pure"] == [.unbounded "pure'"]
#guard spineOf #[.cls "p" "Point" none #[.number "x" false, .number "y" true]]
  == [.unbounded "«p.x»", .unbounded "«p.y»", .opaque "p"]
#guard spineOf #[.cls "s" "Span" none #[.cls "p" "Point" none #[.number "x" false] false]]
  == [.unbounded "«s.p.x»", .opaque "«s.p»", .opaque "s"]

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
