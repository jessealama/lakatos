import Tarski.Project

/-! A correspondence obligation, proved for a symbolic argument by `simp`
with the evaluator's own set.

This is the shape stage C is for: the evaluator's answer to a call,
projected into the model's terms, *equals* the model's answer, injected.
The argument is a free `Float`, so the two obligations below are theorems
about the declaration rather than about one call of it — and the proof is
`simp [tarski_eval, …]` with no hand-written unfolding at all, which is
what `Tarski/Simp.lean` exists to make possible.

The closing recipe for a guarded body is a **case split on the `Bool`**
the comparison denotes, `by_cases h : Float.lt a 0.0 = true`, and not a
`split` on the goal: `split` picks the projection's own outer `match`,
which is not the branch in question. #481's tactic has to split the
`Float.lt`, `Float.le`, and `JsVal.strictEq` Bools an emitted guard is
built from, on both sides at once.

A model and a program must also spell a numeric literal the same way:
`(0 : Float)` elaborates to `OfNat.ofNat` and `(0.0 : Float)` to
`OfScientific.ofScientific`, which are defeq but not syntactically equal,
and `simp` compares syntax. Both sides here say `0.0`.

**What is stated but not proved, and why.** The issue's own `Gate` — a
private field, a throwing constructor, and a getter — is past what Lean's
kernel will check, and so is its constructor on its own. Measured on this
branch with `maxHeartbeats 4000000` and `maxRecDepth 8000`: the
constructor obligation elaborates and then runs past seven minutes
without an answer, and the full getter obligation timed out in the
kernel after eight minutes while this slice was being planned. The
ceiling is the heap's representation, not the class machinery, and #471
owns it — `Test/Tarski/ClassSimpTest.lean` records the same wall. So
`Gate` is stated below as `#eval` pins at two witnesses. When #471 lands,
the `Gate` obligation is the first example's two-line proof with
`closure` and `model` swapped, and this paragraph goes. -/

open Tarski Js

-- A class evaluation allocates a prototype, a constructor object, and a
-- cell per declared name before the constructor's first statement runs,
-- and a symbolic argument keeps both branches alive, so `simp`'s own
-- recursion needs more room than a closed program's.
set_option maxRecDepth 8000

/-! ### A free function, both branches -/

/-- `function f(a) { if (a < 0) throw new RangeError("neg"); return a; }` -/
private def closure : Program :=
  [ .funcDecl "f" ["a"]
      [ .ifStmt (.binary .lt (.ident "a") (.numLit 0.0))
          (.throwStmt (.new (.ident "RangeError") [.strLit "neg"])) none,
        .returnStmt (some (.ident "a")) ] ]

/-- The model `lakatos prove` would prove against: the guard, the throw's
kind, and the returned value, and nothing about the heap. -/
private def model (a : JsNumber) : JsM JsNumber :=
  if Float.lt a 0.0 then .error (.error "RangeError") else .ok a

example (a : Float) :
    project readNumber (runScript (closure ++ [.exprStmt (.call (.ident "f") [.numLit a])]))
      = some (Outcome.ofModel (model a)) := by
  simp [tarski_eval, closure, model]
  by_cases h : Float.lt a 0.0 = true <;> simp [tarski_eval, h]

/-! ### A class, through an own field -/

/-- The model of `class A { constructor(v) { this.x = v; } }`: one field,
read back by name. -/
private structure AModel where
  x : JsNumber
deriving Repr, DecidableEq

/-- The per-class reader, built from the two field primitives the way an
emitted one will be — and pattern-matching on `Value`, because a reader
written as a `do` block over an unmatched one lets `simp` unfold it
inside `match` arms that are already dead. -/
private def readA (h : Heap) : Value → Option AModel
  | .obj r =>
    match readOwnField h (.obj r) "x" with
    | some w =>
      match readNumber h w with
      | some n => some { x := n }
      | none => none
    | none => none
  | .prim _ => none

/-- `class A { constructor(v) { this.x = v; } }` -/
private def closureA : Program :=
  [ .classDecl "A"
      { name := some "A", superClass := none,
        elements := [.ctor ["v"] [.exprStmt (.assign (.member .this "x") (.ident "v"))]] } ]

private def modelA (a : JsNumber) : JsM AModel := .ok { x := a }

example (a : Float) :
    project readA (runScript (closureA ++ [.exprStmt (.new (.ident "A") [.numLit a])]))
      = some (Outcome.ofModel (modelA a)) := by
  simp [tarski_eval, closureA, modelA, readA]

/-! ### The issue's `Gate`, stated and witnessed

The obligation this file would state is

```
example (a : Float) :
    project readNumber (runScript (gate ++ [readLo a])) = some (Outcome.ofModel (modelG a))
```

with `modelG a := if Float.lt a 0.0 then .error (.error "RangeError") else .ok a` —
the same two lines as the first example. It is #471's to make checkable.
What holds today is each branch at a witness. -/

/-- `class Gate { #lo; constructor(a) { if (a < 0) throw new RangeError("neg");
this.#lo = a; } get lo() { return this.#lo; } }` -/
private def gate : Program :=
  [ .classDecl "Gate"
      { name := some "Gate", superClass := none,
        elements :=
          [ .field false (.«private» "lo") none,
            .ctor ["a"]
              [ .ifStmt (.binary .lt (.ident "a") (.numLit 0.0))
                  (.throwStmt (.new (.ident "RangeError") [.strLit "neg"])) none,
                .exprStmt (.assign (.privateMember .this "lo") (.ident "a")) ],
            .method .getter false "lo" [] [.returnStmt (some (.privateMember .this "lo"))] ] } ]

/-- `new Gate(a).lo` -/
private def readLo (a : Float) : Program :=
  gate ++ [.exprStmt (.member (.new (.ident "Gate") [.numLit a]) "lo")]

/-- info: some (Tarski.Outcome.value 5.000000) -/
#guard_msgs in
#eval repr (project readNumber (runScript (readLo 5.0)))

/-- info: some (Tarski.Outcome.error "RangeError") -/
#guard_msgs in
#eval repr (project readNumber (runScript (readLo (-1.0))))
