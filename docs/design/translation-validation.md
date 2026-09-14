# Translation validation — design

Date: 2026-09-14. Grilled with Jesse to completion (all branches resolved).
Stage C of the tarski epic (#376); the design issue is #396.

> This is a dated design record; it is not updated to track the code. For
> current behavior, `spec/semantics.md` and the engines' own docs are
> authoritative.

## What this closes

A `Theorem` from `lakatos prove` is a kernel-checked statement about a
shallow model of a declaration: a Lean `def` the emitter writes from the
TypeScript source. The trust section of `spec/semantics.md` states the gap
plainly: only the primitives are shared with the `tarski` evaluator, the
emitter's translation of control flow is trusted, and nothing proves that
the model of any given declaration is what the evaluator would run.

Stage C closes that gap per declaration. Next to each shallow `def` the
artifact carries the declaration's AST and a proof that running the
evaluator on that AST gives the same outcome as the `def`, on every typed
input. After that the AST plus the evaluator is the definition of truth,
the shallow `def` is a derived normal form, and the emitter is no longer
trusted, because each run checks its output. `@ensures` proofs stay
exactly as cheap as today: the ladder still proves against the shallow
`def`; the correspondence is a separate theorem, proved once per
declaration.

Driver, the fixture the emitter already handles end to end:

```ts
export class Gate {
  #lo: number;
  constructor(a: number) {
    if (a < 0) throw new RangeError("neg");
    this.#lo = a;
  }
  get lo(): number {
    return this.#lo;
  }
}
export function add(a: number, b: number): number {
  return a + b;
}
```

Today thales emits `TsModel.add : JsNumber → JsNumber → JsM JsNumber`, a
`structure TsModel.Gate`, `TsModel.Gate.construct : JsNumber → JsM
TsModel.Gate`, and `TsModel.Gate.lo : TsModel.Gate → JsM JsNumber`, where
`JsM α = Except JsError α` and `JsError.error "RangeError"` is what the
`throw` lowers to. The evaluator (`tarski/Tarski/`) runs a `Program` from
`Heap.initial` in `EvalM = ExceptT Completion (StateT Heap Option)`, where
`none` is divergence and a `throw` carries a heap object.

## D1. The obligation: full equality with `some`

For every validated declaration the artifact states

    ∀ args, project read (runScript (closure ++ [call args])) = some (Outcome.ofModel (shallow args))

read as: the evaluator converges on every typed input, and its outcome,
projected into the model's terms, is the shallow `def`'s outcome, value
for value and error kind for error kind.

Rejected: one-sided refinement (`runScript … = some r → shallow args = r`),
which tolerates evaluator divergence. It costs nothing in the fragment,
which is loop-free (`for` and `while` are `Inappropriate` today), but a
wrong emitter could hide behind divergence once the fragment grows, and
`@ensures` is partial correctness, so the transfer we want is: a run that
returns satisfies the property because the model does. Rejected: comparing
values only and treating any two throws as equal, which is weaker than
what the shallow `def` already claims (it names the kind).

The quantification is over the declared TypeScript parameter types, the
same domain every binder already ranges over. Arguments are spliced into
the AST as literals (`Expr.numLit a`, `Expr.boolLit b`; a keyword union
dispatches on its tag). Nothing is claimed about a caller that passes a
value outside the declared type.

## D2. The projection, owned by tarski

`Tarski/Project.lean` (name provisional; it is the evaluator's side of the
correspondence and mentions nothing of thales) defines

    inductive Outcome (α : Type)
      | value (a : α)
      | error (kind : String)   -- ErrorKind.name
      | other

    def project (read : Heap → Value → Option α)
        : Option (Except Completion (Option Value) × Heap) → Option (Outcome α)

    def Outcome.ofModel : JsM α → Outcome α
      | .ok a => .value a
      | .error (.error kind) => .error kind

with `project`:

- `none` stays `none` (divergence);
- `some (.ok (some v), h)` is `.value a` when `read h v = some a`, else
  `.other`;
- `some (.error (.throw (.obj r)), h)` is `.error kind.name` when the
  object at `r` has `[[Prototype]]` equal to `kind.protoRef` for one of
  the seven `ErrorKind`s (fixed refs 0–6 in the realm), else `.other`;
- every other completion, and a thrown primitive, is `.other`.

`.other` is an outcome no shallow result equals, so an obligation over a
declaration that throws a non-error, returns `undefined`, or returns a
value the reader refuses cannot be established. That is the intended
reading of "the fragment does not say this".

Readers are `readNumber`, `readBool`, the keyword-union readers, and one
emitted reader per class (D4). `Outcome.ofModel` sends the model's
`"type-projection"` error to `.error "type-projection"`, which no run
produces; a shallow `def` that reaches a throwing projection is therefore
"not established", which is correct: that projection is the emitter being
conservative, and the record of it belongs in the `model` field, not in a
verdict.

**Error kinds (decided).** The emitter today lowers `throw new X(...)` to
`JsError.error "X"` for any identifier `X`, arguments dropped. It is
tightened to the seven builtin kinds (`Error`, `TypeError`, `RangeError`,
`ReferenceError`, `SyntaxError`, `EvalError`, `URIError`); any other
`throw` becomes a residual site, so it is `Inappropriate` on the path that
reaches it, as a thrown non-error already is by the tarski spec. The
projection then needs no per-program table and no reading of the `name`
property. Rejected: resolving `X` against the run's own `X.prototype`
(ties the projection to the program's environment, and a `throw new
Box()` would give the kind `Box` a meaning the model never had).

## D3. Which declarations, and what program runs

Every declaration the emitter models and does not taint: exported and
module-level functions, module constants (including derived constants),
class constructors, methods, getters, and static members. The program is
the ESTree of the declaration's dependency closure, in module order
(imported constants, callees, the class the member belongs to), followed
by one statement that calls the declaration:

| shallow                         | final statement       | reader              |
| ------------------------------- | --------------------- | ------------------- |
| `TsModel.add a b`               | `add(a, b)`           | `readNumber`        |
| `TsModel.K`                     | `K`                   | by `K`'s type       |
| `TsModel.Gate.construct a`      | `new Gate(a)`         | `TsModel.Gate.read` |
| `TsModel.Box.scale self k` (D4) | `new Box(x).scale(k)` | `TsModel.Box.read`  |
| `TsModel.Gate.lo self` (D4)     | `new Gate(a).lo`      | `readNumber`        |
| `TsModel.Box.origin` (static)   | `Box.origin()`        | by its type         |

`runScript` returns the completion value of that last expression
statement, which is what `project` reads.

**AST provenance (decided).** The AST is produced by tarski's parser
bridge (`tarski/frontend/`, the typescript-estree path `exe` and the
test262 runner use), not by the emitter's own walk of tsc. The frontend
runs the bridge on the source file, embeds the ESTree JSON of the closure
in the emission JSON (`schemas/thales-emission.schema.json` gains a field
on each declaration), and `thales-emit` links `Tarski.Decode`, decodes it,
and renders the resulting `List Stmt` as a Lean term next to the `def`.
The emitter chooses which declarations are in the closure, never how they
read. Rejected: the emitter writing the Lean AST itself (it stays trusted
for the AST, which defeats the goal); embedding the JSON and decoding
inside the proof (simp would have to evaluate the decoder). A closure the
decoder reports as `unsupported` gives "not established" for that
declaration, naming the construct.

## D4. Classes: replay construction in one closed run

The shallow side quantifies over the constructor's image (the class-valued
binder design): `∀ x, ∀ self, TsModel.Box.construct x = .ok self → …`.
The evaluator side has no structure, only a heap ref. Decided: the
obligation for a member keeps that spine and runs the construction in the
same closed program,

    ∀ (x : JsNumber) (self : TsModel.Box), TsModel.Box.construct x = .ok self →
    ∀ (k : JsNumber),
      project TsModel.Box.read (runScript (closure ++ [ new Box(x).scale(k) ]))
        = some (Outcome.ofModel (TsModel.Box.scale self k))

Class-typed parameters are constructed the same way, one `new` per
binder. Only the argument values are symbolic; every allocation, every
prototype lookup, and every field read happens on a concrete heap, so
`simp` can partially evaluate them. The domain is exactly the class-binder
domain both engines agreed on: instances some constructor call returns
normally. The over-approximation the class-valued-binders record already
states (a subclass or a private constructor) is unchanged; `extends` is
`Inappropriate` today.

The constructor's own obligation is the `new Gate(a)` row of D3, read back
by `TsModel.Gate.read : Heap → Value → Option TsModel.Gate`, a function
the emitter writes next to the `structure` from tarski's field-read
primitives: one private-field read per `#field`, one own-property read per
public field, each through the field's reader. Class-valued results
(`scale` returning a `Box`) and class-valued fields use the same readers.

Rejected: a representation relation over a symbolic heap (`∀ h r self,
Box.read h r = some self → …`). It is more general and compositional, but
the heap is then a variable, every field read needs a rewrite lemma from
the hypothesis, `simp` has no concrete heap to evaluate, and it claims
more than the binder domain.

**Constraints on #384 (the evaluator's classes), decided here so the
plan for #384 does not drift:**

- Public fields are ordinary own properties of the instance. Private
  fields live in a second list on `Obj`, `privateFields : List (String ×
Value)`, keyed by the `#name`, so they are unobservable to `in` and
  `Object.keys` (test262 conformance) and readable by name (the reader).
  Rejected: a brand-keyed table on the heap (the reader would need the
  brand and the table); private names as plain `"#v"` properties
  (observable, fails the class slice).
- Methods and getters are closures on the class's prototype object;
  getters are accessor entries. `this` stays the existing `"this"` cell
  binding pushed by `callFunction`. Construction runs field initializers,
  then the constructor body, in that order.
- The standing constraints stay: `Value.prim` wraps `JsVal`; intrinsics
  at fixed heap refs and `Heap.initial` a literal, so a closed run from it
  is concrete; the interpreter is one `partial_fixpoint` block with
  exactly two opaque catch sites (`catchReturn`, `attempt`) and their
  monotonicity lemmas, and `callFunction` goes through `catchReturn`, so
  its partial-evaluation lemma on a concrete body is load-bearing;
  `Decode.lean` is the only place that says `unsupported`; loop arms never
  enter a simp set.

## D5. Residuals: no obligation, reported as unvalidated

A declaration with a residual site keeps a shallow `def` containing a
`noncomputable opaque`, and a `Theorem` can be issued when the property
never reaches it. Decided: such a declaration gets no obligation. Its
`model` field (D8) says `unvalidated` with the residual's docstring as the
reason (`'**' is not supported`), the same text the `Inappropriate`
verdict uses. A declaration the emitter refuses outright has no `def` and
nothing to validate.

Rejected for now, filed as a follow-up: defining the residual as the
evaluator's own result on its sub-AST, kept irreducible for the ladder.
It would make the obligation hold for tainted declarations too, but the
residual would need the enclosing environment threaded through and it
reopens the opaque-residuals design. Rejected: an on-path conditional
obligation (a path predicate per residual site, on both sides).

## D6. Scheduling: a per-declaration command with its own channel line

`thales-emit` emits, right after each validated declaration's `def` and
before that declaration's `#thales_prove` commands,

    #thales_validate "path/to/file.ts" "Box#scale" := <obligation>

The command runs `simp` with tarski's partial-evaluation set (the
attribute list the `EvalSimpTest`/`CallSimpTest` examples use, made a
named simp set owned by tarski), then `js_norm`, then `split <;> simp`,
under its own heartbeat budget (`thales.validateHeartbeats`, sibling of
`thales.heartbeats`). On success it adds the theorem. Success or not, it
prints one line on a second sentinel,

    thales-model:{"file":"…","function":"Box#scale","status":"validated"}
    thales-model:{"file":"…","function":"add","status":"unvalidated","reason":"the run of 'add' did not reduce to its model"}

and never aborts the artifact. `run.ts` reads both sentinels and joins the
model line onto every annotation of that function. The unsolved goal of a
stuck `simp` goes to the diagnostics stream, not the envelope.

Rejected: a plain emitted `theorem … := by simp` (a failure is an
elaboration error: the artifact dies, every annotation in the file becomes
a prover `Error`, and there is no separate budget); proving inside each
`#thales_prove` (re-proves a declaration fact once per annotation, keyed
by a property identity).

## D7. Failure: verdicts unchanged, the field carries the status

`simp` can only get stuck, never prove the obligation false, so "not
established" covers both a real emitter/evaluator disagreement and a
missing rewrite lemma. Decided: a correspondence that is not established
changes no verdict. A `Theorem` stays a `Theorem`: it is, as the trust
section says, a statement about the shallow model, and the new field is
the trust marker, the way `axioms` records `native_decide` without
downgrading. The CLI's human rendering appends the status to `PROVED` when
it is not `validated`.

Statuses: `validated`; `unvalidated` with a reason that is one of the
residual's construct (D5), "did not reduce to its model" (stuck), the
decoder's `unsupported` construct (D3), or "budget" (heartbeats
exhausted).

Rejected: downgrading `Theorem` to `Error` on that declaration (loud, but
early on a stuck `simp` is far more likely a missing lemma than a real
mismatch, and the other verdicts would still print as if the model were
fine); downgrading every verdict (throws away `CounterSatisfiable`
witnesses that `refute` can check on Node regardless of the model).

## D8. The envelope field

Every prover-produced annotation gains

    "model": { "status": "validated" }
    "model": { "status": "unvalidated", "reason": "…" }

required on the proven variant (next to `axioms`), optional on `GaveUp`,
`Timeout`, `CounterSatisfiable`, and `Inappropriate` from the prover,
absent from `enumerated`, `budget`, and every refuter output, which know
nothing of a model. Nested, so it never collides with `reason`. The store
(`engines/thales/tests/fixtures/envelopes.expected.json`) is regenerated
once, `UPDATE_ENVELOPES=1 LAKATOS_PROVE_E2E=1` from `engines/thales`, then
prettier. `tests/verdict-contract.test.ts` gains the model line's shape.

Rejected: a flat `model` string plus `modelReason` (a second field and a
naming pattern the envelope does not otherwise use); the field on proven
only (a `GaveUp` on an unvalidated model would look like any other).

## D9. What this does and does not claim

- The trusted base moves from "the emitter's translation" to typescript-
  estree, `Tarski.Decode`, the evaluator, and the Lean kernel. The
  evaluator's fidelity is still measured by test262, not asserted.
- A `validated` model says the shallow `def` is what the evaluator computes
  on the declaration's AST for every typed input. It does not say the
  program is correct, that untyped callers behave, or that a declaration
  the model refuses would run.
- The class-binder over-approximation stands: an instance not in the
  constructor's image is outside every claim.
- `refute` still runs on Node; the second limit in the trust section is
  untouched.

The trust section's first limit ("only the primitives are shared") becomes
per-declaration: the envelope's `model` field says, for each verdict,
whether the model was proved equal to the evaluator, and why not when it
was not.

## D10. Implementation issues, in dependency order

All children of #376, each with a worked example. Filed 2026-09-14 as
#478 through #483; the parked follow-up is #484.

1. **Emitter tightening** (#478): `throw new X(...)` accepted for the seven
   builtin kinds only; others residual. Store regeneration. Unblocked.
2. **tarski projection** (#479): `Outcome`, `project`, the readers, the fixed-ref
   error-kind map, the private and own field-read primitives, the named
   partial-evaluation simp set, and a Lean test that proves one symbolic-
   argument obligation through `new` and `callFunction` by `simp`.
   Blocked by #384.
3. **AST plumbing** (#480): the frontend calls the bridge, the closure's ESTree
   rides in the emission JSON and its schema, `thales-emit` decodes it via
   `Tarski.Decode` and renders the `List Stmt`. Blocked by 2.
4. **`#thales_validate`** (#481) for functions and module constants, the
   `thales-model:` line, its budget, `run.ts` parsing. Blocked by 3.
5. **Class obligations** (#482): constructor, method, getter, static replay; the
   per-class reader emitted next to the `structure`. Blocked by 4.
6. **Product** (#483): the `model` field, envelope schema, `run.ts` join, CLI
   rendering, verdict-contract test, store regeneration, and the trust
   section rewrite plus the README sentence. Blocked by 4 (functions
   validate before classes do; the field's `unvalidated` covers the rest
   until 5 lands).

Follow-up, parked (#484): the residual-as-evaluator-result idea from D5.
