# CLAUDE.md

Thales is lakatos's proof engine. It backs `lakatos prove`: annotated TypeScript is emitted as plain Lean 4, Lean attempts to prove each `@ensures` property against a model of each function, and one SZS verdict per annotation comes back to the CLI as a JSON line.

Two halves in two languages:

- **`frontend/` (TypeScript)** — the emitter. Root-package code: compiled by the root `tsconfig.json`, tested by the root vitest suite. Start at `frontend/src/emission.ts` (tsc AST → per-declaration JSON, and the classification of what it cannot map) and `frontend/src/run.ts` (lake/lean orchestration, verdict-line parsing).
- **`ThalesDsl/` + `Js/` + `ThalesEmit/` (Lean 4)** — the prover, the JS-semantics library it draws on, and the renderer behind the `thales-emit` executable. Start at `ThalesDsl/Prove.lean` (the tactic ladder) and `Js/Runtime.lean` (the semantic domain). Toolchain pinned in `lean-toolchain`.

Annotation parsing is not here: discovery, extraction, and prefix/formula parsing live in `lemma/`; the Lean side never sees Lemma syntax.

Docs under `docs/adr/`, `docs/specs/`, `docs/beyond-typescript.md`, and `CHANGELOG.md` predate the plain-Lean rewrite and still describe the removed whole-file compiler (its `Thales/` library, `thales` executable, TH-code diagnostics). Trust the code, not those. `CONTEXT.md` holds the engine's vocabulary.

## Common commands

From `engines/thales/`:

```bash
lake build                       # Js and ThalesDsl (the default targets)
lake build ThalesDslTest         # Lean tests under Test/
lake env lean Test/Js/NormTest.lean           # one Lean test file in isolation
lake build thales-emit           # the emission executable (not a default target)
lake build ThalesEmit            # the renderer's library; prove needs its .olean too
npm run check:verdict-channel    # verdict-line contract over tests/fixtures/*.lean
npm run check:envelopes          # emission envelopes against stored expectations
                                 # (LAKATOS_PROVE_E2E=1 adds the corpus manifest)
UPDATE_ENVELOPES=1 LAKATOS_PROVE_E2E=1 npm run check:envelopes   # regenerate the store
```

From the repo root (the frontend is root-package code):

```bash
npx tsc -p tsconfig.json                      # build (the check scripts need this first)
npx vitest run engines/thales/frontend/tests  # frontend unit tests
npm run format:check                          # prettier, whole repo, one config
LAKATOS_PROVE_E2E=1 npx vitest run tests/e2e.test.ts   # full prove e2e (needs Lean)
```

Always wrap `lake env lean` invocations in a timeout when running them by hand; a bad artifact can grind indefinitely. The check scripts load the _built_ frontend (`scripts/harness.js`), so the sentinel, the parse, and the lake invocation are production's, never a copy.

## The prove pipeline

`lakatos prove` (root `src/cli.ts`) runs one spine:

1. **Discover + extract** — lemma finds `@ensures` annotations; malformed ones become `InputError` entries, and the CLI's island typing refuses type faults and unexported references per annotation before the emitter sees them.
2. **Emit** — `frontend/src/emission.ts` + `emission-artifacts.ts` write per-declaration JSON per annotated file into the run directory's `thales/` mirror; a file whose annotations are all classified gets no artifact.
3. **Render + run** — `frontend/src/run.ts`: `findEngineRoot()` walks up to the lakefile, then `lake build`, `lake build thales-emit`, `thales-emit` per artifact, `lake env lean` per file (timeouts `BUILD_TIMEOUT_MS` 600 s, `EMIT_TIMEOUT_MS` 120 s, `LEAN_TIMEOUT_MS` 300 s; `spawn` is injectable for tests). A failing artifact is a per-file `FileFailure`; the run completes and healthy verdicts still ship.
4. **Join** — root `src/envelope.ts` matches verdict lines to annotation identities; missing, duplicate, surplus, or unrepresentable statuses make the run unhealthy (NotTried envelope, stderr diagnostics, exit 2).

### Emitter invariants the code will not teach you

- Everything an annotation's fate can be settled by is settled frontend-side, before Lean. An unmappable construct or an operator outside the model (`**`, the bitwise family) in a signature, a statement, or a formula classifies `Inappropriate`, naming the construct; the engine's own gaps classify `Error`; a safe-integer-clamped range classifies `NotTried` / `unsupported-range`. Classified annotations never reach Lean.
- **Classification travels.** Every declaration the walk cannot model registers as a failed declaration, and a use of it — call, read, binder type, formula atom — reports that declaration's own reason, never "engine broken". Registries are keyed by module and name together.
- **A body degrades on one thing only**: the first statement outside the slice. A refusal at an _expression_ inside a body becomes a residual site instead — a `noncomputable opaque` over the modeled scope, valued in `JsM`, carrying the refusal text as its docstring — and every callable reaching one is tainted `noncomputable` so the evaluation rung cannot prove through it. Writes (`=`, `++`, `delete`) never residualize: a site would hide the mutation. Formulas never residualize.
- **Rendering is quotations only.** `thales-emit` builds every line via `TSyntax` quotation and Lean's pretty-printer, never string concatenation (the one override, `ThalesEmit/Format.lean`, keeps `return` on its argument's line). Each printed obligation is parsed back and its spine compared to the IR (`ThalesEmit/RoundTrip.lean`), so renderer drift fails the emission by name instead of degrading a verdict.
- **Names never collide by construction.** Models live under `TsModel` with call sites qualified; a dependency's models take its entry-relative path as one guillemet component; a binder spelled like the artifact's own vocabulary (`pure`, `ballIco`, `Float`, `self`) is primed; a source binding of `NaN`, `Infinity`, `undefined`, `null`, `Math`, or `Number` shadows the builtin — those are fallbacks, never keywords.
- **Truthiness has no model.** Conditions, `!`/`&&`/`||` operands, and `Object.is` arguments must be boolean-shaped; a number is refused there. Unions and optionals ride the wire as one `JsVal` binder; reads at a number position are the throwing projection `JsVal.toNumber` — the model refusing coercion, not a claim JS throws.
- Emitted artifacts pin `set_option autoImplicit false`: they run under lean's defaults, not the lakefile's options.
- `scripts/check-envelopes.js` compares projected envelope entries to `tests/fixtures/envelopes.expected.json`; `UPDATE_ENVELOPES=1` insists on the full manifest so the store never goes partial. Rendering rules are pinned as syntax guards in `Test/ThalesEmit/RenderTest.lean`; the goldens under `tests/fixtures/*.emitted.lean.expected` are readability pins only. **A new emission shape adds a guard, not a golden.**

## The Lean side

| Module                                                                | Role                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| --------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Js/Runtime.lean`, `Js/Number/Basic.lean`                             | The domain: `JsM α := Except JsError α`, `JsNumber := Float`, `floatNaN`. **Computability is the invariant** — `decide` must evaluate models over bounded domains.                                                                                                                                                                                                                                                                                                                                    |
| `Js/Val.lean`                                                         | The tagged `JsVal` domain for unions, optionals, and booleans: `toNumber`/`toBoolean` (throwing projections), `typeof`, `strictEq`, `sameValue`.                                                                                                                                                                                                                                                                                                                                                      |
| `Js/Binders.lean`                                                     | Binder-domain meaning: `floatInf` and `ballIco` (bounded ∀ over `[lo, hi)`) with its `Decidable` instance. The witness scans live in `ThalesDsl/Binders.lean`: lakatos owns the search, the library owns the meaning.                                                                                                                                                                                                                                                                                 |
| `Js/Norm.lean` (+ `Js/NormAttr.lean`)                                 | The `js_norm` simp set: what lets pure-looking code shed its monadic wrapping so the closers see bare arithmetic; dual-tagged for grind. A lowered branch is split into one obligation per arm carrying its condition — the only shape in which a literal arm becomes a ground term. Vanilla Lean has no binary64 theory, so each recurring residual goal is one lemma to add here.                                                                                                                   |
| `Js/Number/FloatOps.lean`, `Constants.lean`                           | Binary64 operations JS has and Lean does not (`tsRem`, the roundings, `tsSign`, `tsFround`, `tsMin`/`tsMax`, the integer predicates, `sameValue`) and the `Math`/`Number` constants under their source spellings. Built from `Float.Model`, never `extern`, so the kernel can reduce them; `MAX_VALUE`/`MIN_VALUE` are spelled by bits because their decimals do not reduce.                                                                                                                          |
| `Js/Number/FloatFacts.lean`, `FloatOpsFacts.lean`, `FroundFacts.lean` | Kernel-checked theory about binary64 and the models above (monotonicity against a bounded constant, order transitivity and totality away from NaN, the roundings' and clamps' defining inequalities). Residual goals are over `Float`, whose every op is `pack (op (unpack ..))`, so an `UnpackedFloat` fact reaches one only through the `Canonical` round-trip.                                                                                                                                     |
| `ThalesDsl/Prove.lean`                                                | Options `thales.heartbeats` and `thales.maxEvaluatedElements`, and `attemptLadder`: kernel decide, compiled evaluation (bounded domains only, capped by element count since it cannot be interrupted), then simp/omega and grind on the residual. Each rung gets its own heartbeat window so a blowout falls through instead of consuming the annotation. Every proof is kernel-checked via `addDecl`; the evaluation tier admits an axiom, which is why reasons read trust off the theorem's axioms. |
| `ThalesDsl/ProveTerm.lean`                                            | `#thales_prove`: recovers binder structure from the payload's spine (`ballIco` heads, `∀ (b : Bool)`, guard hypotheses) and synthesizes the witness search with guards threaded in. The bare form reports the `NotTried` stub, so the envelope never changes shape on degradation.                                                                                                                                                                                                                    |
| `ThalesDsl/Verdict.lean`                                              | `Identity` (the `[file, function, property]` triple shared with pabst), the closed `Szs` set, and the sentinel-framed JSON emitter.                                                                                                                                                                                                                                                                                                                                                                   |
| `ThalesEmit/`                                                         | `Json.lean` (strict IR decoding: an unknown kind or missing field fails the run by name), `Render.lean` (IR → `TSyntax` under `Unhygienic`), `Artifact.lean` (syntax → text with echo comments), `RoundTrip.lean`, `Format.lean`, `Main.lean` (JSON in, artifact out, any failure one stderr line and exit 1).                                                                                                                                                                                        |

## The verdict channel

Each `#thales_prove` prints exactly one line: `thales-verdict:` + compact JSON `{identity, szs, reason, axioms?, counterexample?}`. Stdout is also Lean's diagnostic stream; only sentinel-framed lines are contract. An empty `reason` is a contract violation, contained like any other malformed line.

- `Theorem` — a rung succeeded. `axioms` names the non-standard axioms the proof rests on (empty for kernel-checked; `native_decide`'s per-proof axiom is reported under the stable spelling `Lean.ofReduceBool`).
- `CounterSatisfiable` — false on the bounded domain with a concrete witness (`counterexample`: binder → value). Falsity established where the elaborator cannot evaluate a `Float` from a large integer ships without a witness as `GaveUp` instead: established falsity is never given back for the cost of illustrating it.
- `GaveUp` — the ladder exhausted; the reason carries the residual goal. A rung that blows `maxRecDepth` has failed, the annotation has not: the ladder falls through.
- `Inappropriate` — outside the model, not beyond the engine: an unmapped construct, a refused operator, or a path through a residual site (the reason lists the sites' constructs). `Error` stays reserved for the engine breaking, and names the phase that failed.
- `NotTried` — no structured property (the bare-payload degradation path).
- `Timeout` — the per-annotation heartbeat budget (`thales.heartbeats`, overridable via `LAKATOS_PROVE_HEARTBEATS`; 0 is not a budget and is ignored). Later annotations still run with fresh budgets.

The status set lives in exactly two places: the `Szs` inductive here and `SZS_STATUSES` in root `src/szs.ts` (minus the CLI-only `InputError` and `User`). `tests/verdict-contract.test.ts` pins them against each other; everything else derives from the TypeScript side, so a new status is one edit per language.

## Tests

- `Test/Js/`, `Test/ThalesDsl/`, `Test/ThalesEmit/` — one directory per library. Location follows ownership: a `ThalesDsl` import under `Test/Js/` is a boundary violation by inspection.
- `frontend/tests/` — vitest, from the repo root; `run.test.ts` uses the injectable spawn, no real Lean needed.
- `tests/conformance/` — `.ts` fixtures bucketed by the SZS status every annotation in them must receive, run end to end by root `tests/verdict-corpus.test.ts` (gated like the prove e2e). Its README has the bucket conventions.
- CI: `.github/workflows/thales.yml` runs lake build, the Lean tests, both check scripts (envelopes over the full manifest), and the gated e2e + corpus.

## Conventions

- **`autoImplicit` is off** project-wide (`lakefile.lean`); bind implicit and universe variables explicitly.
- **Failure containment over abortion.** A construct the engine can't handle degrades that declaration, that annotation, or that artifact — never the run. New frontend features must preserve this.
- **One verdict line per `#thales_prove`, always**, even for failures the elaborator can see. Annotations the frontend classifies never enter the channel; the CLI joins them from the emission's `classified` list.
- **Boundary rule:** nothing under `Js/` may mention `ThalesDsl` or any emission concern — lakatos owns syntax and search, the library owns meaning.
- **Lean builds here; the frontend builds at the root.** This directory's `package.json` (`thales-dev`) exists only for the check scripts and has no dependencies. Formatting is root-only: one prettier pin, one config.
