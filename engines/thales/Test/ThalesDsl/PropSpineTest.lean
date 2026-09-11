import ThalesDsl

open ThalesDsl Lean Js

/-! The binder spine drives rung selection: a spine that recovers no
binders reports every domain bounded, which spends both decide rungs
enumerating a goal no decision procedure can settle. These pin what each
emitted head is recovered as. -/

/-- The binder kinds a spine recovered, outermost first. -/
def spineKinds (t : TSyntax `term) : List String :=
  (propSpine t).binders.map fun
    | .ranged n .. => s!"ranged {n}"
    | .unbounded n => s!"unbounded {n}"
    | .opaque n => s!"opaque {n}"
    | .bool n => s!"bool {n}"

-- Built unhygienically, the way the parsed artifact text reaches the
-- command: a macro scope on a binder name is a test artifact, not a shape
-- production ever sees.
#eval show CoreM Unit from do
  -- A class binder: its synthesized constructor arguments are ordinary
  -- JsNumber heads, and the instance itself is opaque.
  let t := Unhygienic.run `(∀ («p.x» : JsNumber), ∀ («p.y» : JsNumber),
    ∀ (p : TsModel.Point), TsModel.Point.construct «p.x» «p.y» = .ok p →
      ((pure true : JsM Bool) = pure true))
  let kinds := spineKinds t
  unless kinds == ["unbounded «p.x»", "unbounded «p.y»", "opaque p"] do
    throwError "the class-binder spine is {kinds}"
  -- Never enumerable: the domain is a constructor's image, not a range.
  unless (propSpine t).domains?.isNone do
    throwError "an opaque binder was reported bounded"

#eval show CoreM Unit from do
  -- A boolean constructor argument is a Bool head; the instance stays
  -- opaque, so the spine is still never enumerable.
  let t := Unhygienic.run `(∀ («f.on» : Bool), ∀ (f : TsModel.Flag),
    TsModel.Flag.construct «f.on» = .ok f → ((pure true : JsM Bool) = pure true))
  let kinds := spineKinds t
  unless kinds == ["bool «f.on»", "opaque f"] do
    throwError "the boolean class-binder spine is {kinds}"
  unless (propSpine t).domains?.isNone do
    throwError "an opaque binder was reported bounded"

#eval show CoreM Unit from do
  -- The numeric heads keep their own readings; the constructor-image arm
  -- sits after them and must not claim an `Int` binder whose body is an
  -- implication.
  let t := Unhygienic.run `(∀ (n : Int), 0 ≤ n → ((pure true : JsM Bool) = pure true))
  unless spineKinds t == ["unbounded n"] do
    throwError "the nat head is {spineKinds t}"
  let r := Unhygienic.run `(ballIco 0 5 fun x => ((pure true : JsM Bool) = pure true))
  unless spineKinds r == ["ranged x"] do
    throwError "the ranged head is {spineKinds r}"

#eval show CoreM Unit from do
  -- A `∀` whose body is an implication but not a constructor image is its
  -- own leaf, so nothing downstream reads a binder that is not there.
  let t := Unhygienic.run `(∀ (p : TsModel.Point), (0 : Nat) = 0 → ((pure true : JsM Bool) = pure true))
  unless spineKinds t == [] do
    throwError "a non-image implication was read as a binder: {spineKinds t}"

#eval show CoreM Unit from do
  -- A binder's own bounds — a number binder's endpoints, a nat binder's
  -- nonnegativity — are stepped over, so the binders and guards under
  -- them are read. Search never runs on such a domain, so the bounds
  -- need not be kept.
  let t := Unhygienic.run `(∀ (sf : JsNumber), 0 < sf → sf < floatInf →
    ((pure true : JsM Bool) = pure true) → ((pure true : JsM Bool) = pure true))
  unless spineKinds t == ["unbounded sf"] do
    throwError "the bounded number head is {spineKinds t}"
  unless (propSpine t).guards.length == 1 do
    throwError "the guard under a number binder's bounds was not recovered"
  let u := Unhygienic.run `(∀ (n : Int), 0 ≤ n → ∀ (y : Int),
    ((pure true : JsM Bool) = pure true) → ((pure true : JsM Bool) = pure true))
  unless spineKinds u == ["unbounded n", "unbounded y"] do
    throwError "the binder under a nat binder's bound is {spineKinds u}"
  unless (propSpine u).guards.length == 1 do
    throwError "the guard under a nat binder's bound was not recovered"
  -- Every endpoint spelling the renderer prints is a bound.
  let v := Unhygienic.run `(∀ (x : JsNumber), (-1.5e3) ≤ x → x < -floatInf →
    ∀ (y : Int), ((pure true : JsM Bool) = pure true))
  unless spineKinds v == ["unbounded x", "unbounded y"] do
    throwError "the literal endpoints read as {spineKinds v}"

#eval show CoreM Unit from do
  -- Only a bound on the binder just bound is stepped over: one naming
  -- another binder, or one whose far side is not a literal, is the leaf.
  let t := Unhygienic.run `(∀ (x : JsNumber), ∀ (y : JsNumber), 0 < x →
    ((pure true : JsM Bool) = pure true))
  unless spineKinds t == ["unbounded x", "unbounded y"] do
    throwError "a bound on an outer binder read as {spineKinds t}"
  unless (propSpine t).guards.isEmpty do
    throwError "a bound on an outer binder was read as a guard"
  let u := Unhygienic.run `(∀ (x : JsNumber), ∀ (y : JsNumber), y < x →
    ∀ (z : Int), ((pure true : JsM Bool) = pure true))
  unless spineKinds u == ["unbounded x", "unbounded y"] do
    throwError "a comparison between binders read as {spineKinds u}"
  -- A ranged binder never prints a bound; one under it stays in the leaf,
  -- where the witness search still sees it.
  let v := Unhygienic.run `(ballIco 0 5 fun x => 0 < x →
    ((pure true : JsM Bool) = pure true))
  unless spineKinds v == ["ranged x"] do
    throwError "a bound under a ranged binder read as {spineKinds v}"
  unless (propSpine v).guards.isEmpty do
    throwError "a bound under a ranged binder was read as a guard"

#eval show CoreM Unit from do
  -- `domains?` is the one reading the elaboration takes: the domains the
  -- search enumerates, present exactly when every binder has one.
  let t := Unhygienic.run `(ballIco 0 5 fun x =>
    ballIco (-2) 3 fun y => ((pure true : JsM Bool) = pure true))
  unless (propSpine t).domains? == some [("x", .ico 0 5), ("y", .ico (-2) 3)] do
    throwError "the all-ranged spine reads {repr (propSpine t).domains?}"
  let u := Unhygienic.run `(ballIco 0 5 fun x =>
    ∀ (n : Int), ((pure true : JsM Bool) = pure true))
  unless (propSpine u).domains?.isNone do
    throwError "a spine with an unbounded binder reported domains"
  let v := Unhygienic.run `(((pure true : JsM Bool) = pure true))
  unless (propSpine v).domains? == some [] do
    throwError "a closed leaf is bounded with no domains, not {repr (propSpine v).domains?}"

#eval show CoreM Unit from do
  -- A boolean head is enumerable: two values, no bounds to read past.
  let t := Unhygienic.run `(ballIco 0 3 fun n => ∀ (b : Bool),
    ((pure true : JsM Bool) = pure true))
  unless spineKinds t == ["ranged n", "bool b"] do
    throwError "the boolean head is {spineKinds t}"
  unless (propSpine t).domains? == some [("n", .ico 0 3), ("b", .bool)] do
    throwError "the mixed spine reads {repr (propSpine t).domains?}"
  let u := Unhygienic.run `(∀ (b : Bool), ∀ (x : Int),
    ((pure true : JsM Bool) = pure true))
  unless spineKinds u == ["bool b", "unbounded x"] do
    throwError "the boolean-then-int spine is {spineKinds u}"
  unless (propSpine u).domains?.isNone do
    throwError "a spine with an unbounded binder reported domains"
