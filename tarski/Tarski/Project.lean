import Tarski.Simp

/-! The correspondence projection: an evaluator outcome read in the
model's terms.

`lakatos prove` proves a property of a *model* — a `JsM α` built out of
the `Js` library. The evaluator answers something else entirely: an
`Option (Except Completion (Option Value) × Heap)`, a run that may not
terminate, may end abruptly, and carries a whole heap with it. This
module is the one function that reads the second as the first, so that a
per-declaration correspondence obligation can be *stated*: the evaluator's
answer to a call, projected, equals the model's answer, injected.

**What the projection claims.** `Outcome α` has three constructors and
the third is the point. `value a` says the run returned something the
reader recognized as an `a`; `error k` says it threw an object whose
`[[Prototype]]` is one of the seven `Error` prototypes, `k` being that
kind's `name`. Everything else is `other` — a `break` that crossed the
top, a thrown primitive, a thrown object of any other shape, a run whose
statement produced no value, a value the reader refused. **No model
equals `other`**: `Outcome.ofModel` only ever answers `value` or `error`,
so an obligation that lands on `other` is a failed correspondence rather
than a vacuous one. Divergence is not an `Outcome` at all: the evaluator's
`none` projects to `none`, and a model makes no claim about a run that
never ends, which is what `@ensures`'s partial correctness already says.

**The seven kinds, by prototype.** `errorKindOf` asks the heap for the
thrown object's `[[Prototype]]` and compares it against the seven fixed
`protoRef`s — a table lookup, not a `name` property read, so a script
that assigns `RangeError.prototype.name = "Nope"` cannot change what a
throw projects to, and neither can a `name` own property on the thrown
object. A subclass instance carries its *own* class's prototype, so
`class E extends RangeError {}; throw new E()` is `other`: the model has
no kind for it, and #478 records that as a residual site rather than a
correspondence.

**A private field is found by name, through the constructor's closure.**
The heap alone cannot: `Tarski/Value.lean` makes a Private Name a *cell
reference*, so the `#lo` on an instance is stored under a number, not
under the string `"#lo"`. The spelling is bound in the class's own scope,
which the constructor closed over — so the walk is instance → `proto` →
its own `constructor` property → that closure's `env` → `Env.lookup` of
`"#" ++ name` → `Obj.getPrivate`. Its one assumption is that
`prototype.constructor` is intact; a program that overwrote it reads
`none`, which projects to `other`, which is the safe direction.

Nothing here mentions thales or emission. The per-class readers an
emitted model needs are built *out of* `readOwnField` and
`readPrivateField` on the other side of the boundary. -/

namespace Tarski

open Js

/-- What a run amounts to, once the heap has been read away. `other` is
the outcome no model has, which is what makes a correspondence
obligation say something. -/
inductive Outcome (α : Type) where
  /-- The run returned a value the reader recognized. -/
  | value (a : α)
  /-- The run threw one of the seven `Error` kinds, named. -/
  | error (kind : String)
  /-- Anything else at all. -/
  | other
deriving Repr, DecidableEq

/-- A model's answer as an outcome. Total, `JsError` having one
constructor and carrying the kind's spelling; `other` is unreachable
here, which is the whole of why it is worth having. -/
@[tarski_eval]
def Outcome.ofModel {α : Type} : JsM α → Outcome α
  | .ok a => .value a
  | .error (.error kind) => .error kind

/-- The `Error` kind a thrown value belongs to, by its `[[Prototype]]`
against the seven the realm fixes. A primitive, a reference the heap does
not have, a null prototype, and any other prototype — a subclass's
included — are `none`. -/
@[tarski_eval]
def errorKindOf (h : Heap) : Value → Option ErrorKind
  | .prim _ => none
  | .obj r =>
    match h.readObj r with
    | none => none
    | some o =>
      match o.proto with
      | none => none
      | some p => ErrorKind.all.find? (fun k => k.protoRef == p)

/-- The projection. `read` is how a value is recognized as an `α`: a
plain reader for a primitive, or a per-class one built from the field
readers below. -/
@[tarski_eval]
def project {α : Type} (read : Heap → Value → Option α) :
    Option (Except Completion (Option Value) × Heap) → Option (Outcome α)
  | none => none
  | some (.ok (some v), h) =>
    match read h v with
    | some a => some (.value a)
    | none => some .other
  | some (.ok none, _) => some .other
  | some (.error (.throw v), h) =>
    match errorKindOf h v with
    | some k => some (.error k.name)
    | none => some .other
  | some (.error _, _) => some .other

/-! ### The readers

Each is a pattern match on `Value`, never a `do` block over an unmatched
one: an unconditional equation lets `simp` unfold the reader inside `match`
arms that are already dead, and elaboration does not come back. -/

/-- A `number`. -/
@[tarski_eval]
def readNumber (_h : Heap) : Value → Option JsNumber
  | .prim (.num x) => some x
  | _ => none

/-- A `boolean`. -/
@[tarski_eval]
def readBool (_h : Heap) : Value → Option Bool
  | .prim (.bool b) => some b
  | _ => none

/-- Any primitive, as the library's own tagged value. This is the reader
for a slot a model types as `JsVal` — a keyword union, or a parameter
that admits `undefined` — where the tag itself is what the property
quantifies over. -/
@[tarski_eval]
def readPrim (_h : Heap) : Value → Option JsVal
  | .prim v => some v
  | .obj _ => none

/-- An own *data* property. An accessor property and an inherited one are
both `none`: a field of a model is a field, and a getter is a call. -/
@[tarski_eval]
def readOwnField (h : Heap) : Value → String → Option Value
  | .obj r, key =>
    match h.readObj r with
    | none => none
    | some o => o.getOwn key
  | .prim _, _ => none

/-- A private field, by its `#name`. The name is a cell reference, so it
is resolved the only way the heap allows: through the class scope the
instance's constructor closed over. The module header says why, and what
the walk assumes. -/
@[tarski_eval]
def readPrivateField (h : Heap) : Value → String → Option Value
  | .obj r, name =>
    match h.readObj r with
    | none => none
    | some o =>
      match o.proto with
      | none => none
      | some p =>
        match h.readObj p with
        | none => none
        | some proto =>
          match proto.getOwn "constructor" with
          | some (.obj c) =>
            match h.readObj c with
            | some { callable := some (.closure cl), .. } =>
              match Env.lookup cl.env ("#" ++ name) with
              | some k => o.getPrivate k
              | none => none
            | _ => none
          | _ => none
  | .prim _, _ => none

end Tarski
