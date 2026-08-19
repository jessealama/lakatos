# Thales

Thales is lakatos's proof engine: a TypeScript frontend transcribes `@ensures`-annotated functions into a Lean 4 DSL, and Lean elaboration attempts to prove each property, reporting one SZS verdict per annotation. The user-visible surface is `lakatos prove`; thales itself ships no CLI.

The vocabulary below is for the rewritten engine. The previous compiler's vocabulary (refinement types, prelude library types, TH#### subset diagnostics, the conformance harness) was retired with it; treat any occurrence in older notes as historical.

## Language

### Pipeline vocabulary

**Transcription**:
The frontend pass that pretty-prints tsc's AST into DSL constructor text — `ts_def` declarations for functions, `#thales_prove` commands for annotations. It is a printer, not a checker: there is no intermediate IR, no subset check, and "accept all TypeScript" is its job. What it cannot map it emits anyway, as opaque nodes.
_Avoid_: "compilation", "emission" (the old compiler's terms — they imply a checked lowering)

**Core-constructor grammar**:
The small fixed Lean syntax surface (`ts.id[...]`, `ts.binop[...]`, `ts.call[...]`, `ts.forall(...)`, ...) declared in `Syntax.lean`, mirroring tsc AST node shapes nearly 1:1. Parsing an artifact never fails on unknown meaning; an unknown operator or missing model is an elaboration failure, which is what keeps degradation per-declaration.
_Avoid_: "the DSL's AST" (meaning lives in elab rules, not in a datatype)

**Opaque node**:
`ts.opaque[...]` — the transcriber's encoding of a construct it cannot map, carrying the tsc SyntaxKind name and source position. Elaborating one always fails, so the enclosing `ts_def` degrades alone and the annotation over it becomes `Inappropriate`.
_Avoid_: "unsupported placeholder" (the old compiler's accept-then-fail hazard; opaque nodes are contained by design)

**Artifact / artifact mirror**:
The generated `.lean` file for one source file, written under the target project's `.thales/` directory by the shared mirroring rule (source extension kept: `a.ts` → `.thales/a.ts.lean`). Annotation-free sources get no artifact. Artifacts are regenerated every run and never hand-edited.

**Model**:
The Lean definition a `ts_def` elaborates to, registered in the model registry; this slice types every parameter and result as `Int` over the `TsM` monad. A declaration that fails to model lands in the failed registry instead, with the unmapped construct recorded when an opaque node caused it.

**TsM**:
The semantic domain of models: `Except JsError` today, growing with future slices (state, fuel). The load-bearing property is computability — `decide` must be able to evaluate models over bounded domains, so nothing noncomputable may enter a model's type.

**Bounded quantification (`ballIco`)**:
The half-open-interval ∀ that Lemma binder guards elaborate to, carrying its own `Decidable` instance. It is the reason bounded properties are decidable at all.

### Verdict vocabulary

**Verdict channel**:
The stdout contract between `#thales_prove` and the CLI: one sentinel-framed (`thales-verdict:`) compact-JSON line per annotation, in command order. Unframed stdout is Lean diagnostics, forwarded to stderr by the runner — never part of the contract.
_Avoid_: "output", "log lines" (framing is what makes it a contract)

**Identity**:
The `[file, function, property]` triple keying each annotation, shared with the refutation engine so both engines' results join into one envelope. Function names use the qualified form (`fn`, `Class#method`, `Class.method`).

**SZS statuses (prove)**:
`Theorem` (proved by `decide`, kernel-checked), `GaveUp` (elaborated but the proof attempt failed), `Inappropriate` (unmapped construct in the function or property), `Error` (any other elaboration failure), `NotTried` (no structured property provided). This five-status set must stay in sync with the CLI's `PROVE_STATUSES`; the root suite pins them.
_Avoid_: inventing statuses locally; `Unknown`/`Timeout` are not in the set

**Failure containment**:
The engine's degradation ladder: a bad construct fails one declaration (failed registry), a bad property fails one annotation (its verdict), a bad artifact fails one file (a per-file failure in the run result) — the run always completes and healthy verdicts still ship. Whole-run aborts are reserved for lake build failures and missing engine roots.
_Avoid_: "error handling" (containment is the design property, not incidental recovery)

**Structured property**:
A property the transcriber could express in constructor syntax (bounded int/nat binders, equation or boolean-island body). Anything else is emitted without a body and verdicts as `NotTried` — degradation, not rejection.

### Flagged ambiguities

- **"Compiler"** — colloquially still used for the engine. The old whole-file TS-to-Lean compiler is gone; today the closest thing is the _transcriber_, which is deliberately not a compiler (no checking, no lowering semantics — meaning lives in the Lean elab rules). When precision matters, say transcriber or elaborator.
- **"Conformance"** — the old corpus under `tests/conformance/` defined the retired compiler's correctness and is currently orphaned, pending rebuild as verdict fixtures. The operative checks today are the verdict-channel and transcriber scripts plus the root prove e2e.
- **"Verdict" vs "envelope entry"** — a verdict is the engine-side JSON line; the envelope entry is the CLI-side per-annotation record after joining (which adds `InputError` entries the engine never sees). The engine emits verdicts, never envelopes.
