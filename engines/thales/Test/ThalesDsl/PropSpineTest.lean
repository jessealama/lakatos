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
  unless (propSpine t).ranges?.isNone do
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
  -- A number binder's endpoints are hypotheses in the leaf, the way a nat
  -- binder's nonnegativity is: nothing under them is read, since search
  -- never runs on an unbounded domain.
  let t := Unhygienic.run `(∀ (sf : JsNumber), 0 < sf → sf < floatInf →
    ((pure true : JsM Bool) = pure true) → ((pure true : JsM Bool) = pure true))
  unless spineKinds t == ["unbounded sf"] do
    throwError "the bounded number head is {spineKinds t}"
  unless (propSpine t).guards.isEmpty do
    throwError "a guard under a number binder's bounds was recovered"

#eval show CoreM Unit from do
  -- `ranges?` is the one reading the elaboration takes: the endpoints the
  -- search enumerates, present exactly when every binder has them.
  let t := Unhygienic.run `(ballIco 0 5 fun x =>
    ballIco (-2) 3 fun y => ((pure true : JsM Bool) = pure true))
  unless (propSpine t).ranges? == some [("x", 0, 5), ("y", -2, 3)] do
    throwError "the all-ranged spine reads {repr (propSpine t).ranges?}"
  let u := Unhygienic.run `(ballIco 0 5 fun x =>
    ∀ (n : Int), ((pure true : JsM Bool) = pure true))
  unless (propSpine u).ranges?.isNone do
    throwError "a spine with an unbounded binder reported ranges"
  let v := Unhygienic.run `(((pure true : JsM Bool) = pure true))
  unless (propSpine v).ranges? == some [] do
    throwError "a closed leaf is bounded with no ranges, not {repr (propSpine v).ranges?}"
