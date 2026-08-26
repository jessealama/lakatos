# Thales

Thales is lakatos's proof engine: a TypeScript frontend emits plain Lean 4 for `@ensures`-annotated functions, and Lean attempts to prove each property, reporting one SZS verdict per annotation. The user-visible surface is `lakatos prove`; thales itself ships no CLI.

The vocabulary below is for the rewritten engine. The previous compiler's vocabulary (refinement types, prelude library types, TH#### subset diagnostics, the conformance harness) was retired with it; treat any occurrence in older notes as historical.

## Language

### Pipeline vocabulary

**Emission**:
The frontend pass that walks tsc's AST into per-declaration JSON, which the `thales-emit` executable renders as ordinary Lean — a `def` per function, a `#thales_prove` command per obligation. What it cannot map it does not emit: the frontend classifies that annotation itself, so the artifact only ever carries declarations with a model.

**Classification**:
The frontend's own verdict on an annotation it will not emit: `Inappropriate` when the input is outside the model (an unmapped construct, a refused operator, a class-valued binder), `NotTried` when a safe-integer clamp is the sole blocker, `Error` when the engine is the one at fault. A classified annotation never reaches Lean; the CLI joins its verdict into the envelope alongside the ones Lean reports.
_Avoid_: "unsupported placeholder" (the old compiler's accept-then-fail hazard; classification is contained by design)

**Failed declaration**:
A declaration the emitter could not model, recorded with the construct that stopped it. The refusal travels with the call, so a function calling one degrades the same way — which is what makes a caller of an unmapped import `Inappropriate` rather than `Error`.

**Artifact / artifact mirror**:
The generated `.lean` file for one source file, written under the run directory's `thales/` mirror by the shared mirroring rule (source extension kept: `a.ts` → `<run>/thales/a.ts.lean`). Annotation-free sources get no artifact. Artifacts are regenerated every run and never hand-edited.

**Model**:
The Lean `def` an emitted declaration becomes, under the `TsModel` namespace and tagged `@[js_norm, grind]` so the symbolic rungs can unfold it; this slice types every parameter and result as `Float` — IEEE-754 binary64, the type a TypeScript `number` actually holds — over the `JsM` monad. Binders still quantify over the mathematical integers and coerce in at the call boundary, which is exactly why an interval reaching past the safe-integer range is refused: outside it the coercion stops being injective. A declaration that fails to model is classified frontend-side instead, with the unmapped construct recorded.

**JsM**:
The semantic domain of models: `Except JsError` today, growing with future slices (state, fuel). The load-bearing property is computability — the decide rungs must be able to evaluate models over bounded domains, so nothing noncomputable may enter a model's type. With binary64 bodies this is the only route to a proof at all: vanilla Lean carries no `Float` arithmetic theory, so a domain that cannot be enumerated cannot yet be settled.

**Bounded quantification (`ballIco`)**:
The half-open-interval ∀ that Lemma binder guards elaborate to, carrying its own `Decidable` instance. It is the reason bounded properties are decidable at all.

### Verdict vocabulary

**Verdict channel**:
The stdout contract between `#thales_prove` and the CLI: one sentinel-framed (`thales-verdict:`) compact-JSON line per annotation, in command order. Unframed stdout is Lean diagnostics, forwarded to stderr by the runner — never part of the contract.
_Avoid_: "output", "log lines" (framing is what makes it a contract)

**Identity**:
The `[file, function, property]` triple keying each annotation, shared with the refutation engine so both engines' results join into one envelope. Function names use the qualified form (`fn`, `Class#method`, `Class.method`).

**SZS statuses (prove)**:
`Theorem` (a rung of the ladder proved it; the verdict's `axioms` field lists the non-standard axioms the proof rests on — empty when kernel-checked, the admitted native-evaluation axiom otherwise), `CounterSatisfiable` (the property is false on its bounded domain and a concrete witness was extracted — carried in the verdict's `counterexample` field), `GaveUp` (elaborated but the proof attempt failed, including falsity with no witness to ship: zero binders, or witness extraction degraded), `Inappropriate` (unmapped construct or refused operator in the function or property), `Error` (any other failure), `NotTried` (no structured property provided), `Timeout` (the attempt exceeded the per-annotation heartbeat budget). The set is the `Szs` inductive in `Verdict.lean`, and it must enumerate exactly the CLI's `ProveStatus` (root `src/szs.ts`); the root suite pins them.
_Avoid_: inventing statuses locally; a status the CLI does not know is not on the wire

**Failure containment**:
The engine's degradation ladder: a bad construct fails one declaration (a failed declaration), a bad property fails one annotation (its verdict), a bad artifact fails one file (a per-file failure in the run result) — the run always completes and healthy verdicts still ship. Whole-run aborts are reserved for lake build failures and missing engine roots.
_Avoid_: "error handling" (containment is the design property, not incidental recovery)

**Structured property**:
A property the emitter could express as a plain `Prop` (binders as `ballIco` or `∀` heads, guards as `= pure true` hypotheses, an equation or boolean-island conclusion). An obligation emitted without a payload verdicts as `NotTried` — degradation, not rejection.

**Verdict corpus**:
The end-to-end fixture suite under `tests/conformance/`: `.ts` fixtures in buckets named for SZS statuses, where bucket membership is the entire specification — every annotation in a fixture must receive its bucket's status. A capability upgrade shows up as a `git mv` between buckets, never as an expectation edit.
_Avoid_: "conformance harness" (the retired compiler's whole-file corpus)

### Flagged ambiguities

- **"Compiler"** — colloquially still used for the engine. The old whole-file TS-to-Lean compiler is gone; today the closest thing is the _emitter_, which checks what it can model and classifies the rest rather than lowering everything. When precision matters, say emitter (the frontend) or prover (the Lean side).
- **"Conformance"** — `tests/conformance/` now holds the _verdict corpus_, which defines the prove pipeline's correctness by SZS bucket; in notes older than the rebuild, "conformance" means the retired compiler's whole-file corpus instead. The operative checks today are the verdict-channel and envelope scripts, the root prove e2e, and the verdict corpus.
- **"Verdict" vs "envelope entry"** — a verdict is the engine-side JSON line; the envelope entry is the CLI-side per-annotation record after joining (which adds `InputError` entries the engine never sees). The engine emits verdicts, never envelopes.
