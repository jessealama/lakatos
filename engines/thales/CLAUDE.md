# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working on the thales engine.

## What this engine is

Thales is lakatos's proof engine. It backs `lakatos prove`: annotated TypeScript is transcribed into a Lean 4 DSL, Lean elaborates a model of each function and attempts to prove each `@ensures` property, and one SZS verdict per annotation comes back to the CLI as a JSON line.

This is a ground-up rewrite; the previous whole-file subset-checking compiler (its `Thales/` library, `thales` executable, TH-code diagnostics, and conformance harness) has been removed, and the layers of the new engine are landing slice by slice. If a doc or comment mentions those, it predates the rewrite.

The engine has two halves in two languages:

- **`frontend/` (TypeScript)** — the transcriber. Part of the root npm package: compiled by the root `tsconfig.json` and tested by the root vitest suite. `transcribe.ts` pretty-prints tsc's AST into DSL constructor text (no intermediate IR), `artifacts.ts` writes the `.thales/` artifact mirror, `run.ts` shells out to lake/lean and parses verdict lines.
- **`ThalesDsl/` (Lean 4)** — the elaborator. A lake library (no executable); artifacts are run with `lake env lean`. Pinned toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`).

Annotation parsing is NOT here: file discovery, `@ensures` extraction, and prefix/formula parsing all live in `lemma/` at the repo root. The frontend consumes lemma's parsed output; the Lean side never sees Lemma syntax.

## Common commands

From `engines/thales/`:

```bash
lake build                       # build the ThalesDsl library
lake build ThalesDslTest         # Lean tests under Test/
lake env lean Test/ThalesDsl/ModelTest.lean   # one Lean test file in isolation
npm run check:verdict-channel    # verdict-line contract over tests/fixtures/*.lean
npm run check:transcriber        # transcribe tracer.ts, run it, assert verdicts
npm run format:check             # prettier (this directory has its own pin)
```

From the repo root (the frontend is root-package code):

```bash
npx tsc -p tsconfig.json                      # build (check:transcriber needs this first)
npx vitest run engines/thales/frontend/tests  # frontend unit tests
LAKATOS_PROVE_E2E=1 npx vitest run tests/e2e.test.ts   # full prove e2e (needs Lean)
```

Always wrap `lake env lean` invocations in a timeout when running them by hand; a bad artifact can grind indefinitely.

## The prove pipeline

`lakatos prove` (in root `src/cli.ts`) drives these stages:

1. **Discover + extract** — `lemma/`'s `resolveFiles` and `extractFromSource` find `@ensures` annotations; malformed ones become `InputError` envelope entries.
2. **Transcribe** (`frontend/src/transcribe.ts`) — each function becomes a `ts_def "name" := ts.fn(...) : ts.number { ... }` declaration and each annotation a `#thales_prove "file" "fn" "prop" := ts.forall(...) { ... }` command, all in the DSL's core-constructor syntax (`ts.id[...]`, `ts.binop[...]`, `ts.call[...]`, ...). Constructs the frontend cannot map become `ts.opaque` nodes carrying the tsc SyntaxKind and source position. Unbounded int/nat binders transcribe to their own constructors (`ts.binder["x"](ts.int)` / `ts.nat`). A binder lowers by the domain it _denotes_ — open endpoints folded, nat floored at 0 — so `int ∈ [0, ∞)` is the `ts.nat` binder and `nat ∈ (-∞, 10]` is the bounded `ts.range(0, 11)`; what degrades to the bare command is a non-integer domain or a half-bounded range the DSL has no shape for (any floor other than 0 with no ceiling, or a ceiling with no floor — substituting the safe-range limit would prove a narrower statement than written). Properties that don't fit the structured shape are emitted without a body, which the elaborator reports as `NotTried`. A property whose only blocker is a range endpoint beyond the safe integer range gets no `#thales_prove` command at all — proving over the clamped domain would be a narrower statement than written — and is recorded as a `-- not tried` comment plus an `untried` entry on the transcription, which the CLI reports as `NotTried` with kind `unsupported-range`. Invalid annotations are recorded as `-- skipped` comments.
3. **Write artifacts** (`frontend/src/artifacts.ts`) — one `.lean` file per source file under the `.thales/` mirror (gitignored in the target project; annotation-free files get no artifact).
4. **Run** (`frontend/src/run.ts`) — `findEngineRoot()` walks up from this module looking for the lakefile (absent → `no-project`); then `lake build` once and `lake env lean <artifact>` per file (timeouts: `BUILD_TIMEOUT_MS` 600s, `LEAN_TIMEOUT_MS` 300s; injectable `spawn` for tests). A failing artifact is contained as a per-file `FileFailure` — the run still completes and healthy verdicts still ship.
5. **Join** — root `src/envelope.ts` matches verdict lines to annotation identities; missing, duplicate, surplus, or unrepresentable statuses make the run unhealthy (NotTried envelope, stderr diagnostics, exit 2).

## The Lean side (`ThalesDsl/`)

| Module         | Role                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| -------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Syntax.lean`  | `declare_syntax_cat` grammar for the core constructors (`ts_type`/`ts_expr`/`ts_stmt`/`ts_param`/`ts_binder`/`ts_prop`, including unbounded int/nat binders), the `ts_def` declaration and `#thales_prove` command. Parsing never fails on unknown _meaning_ — that's an elaboration failure.                                                                                                                                                                                                                                                                                                                                             |
| `TsM.lean`     | The semantic domain: `TsM α := Except JsError α`. Computability is the invariant — `decide` must be able to evaluate models over bounded domains. Also `ballIco` (bounded ∀ over half-open `[lo, hi)`) with its `Decidable` instance.                                                                                                                                                                                                                                                                                                                                                                                                     |
| `Norm.lean`    | The `thales_norm` simp set (attribute registered in `NormAttr.lean`): normalization lemmas plus attribute-tagged models — what lets pure-looking code shed its monadic wrapping so omega sees bare Int arithmetic. The set's knowledge is dual-tagged for grind (`ballIco_iff` and the models), so the grind rung can open bounded ∀s and unfold models itself.                                                                                                                                                                                                                                                                           |
| `Model.lean`   | `ts_def` elaboration: `evalExpr`, the `modelExt` registry of successful models, and the `failedExt` registry of failed declarations (with the unmapped construct when an opaque node caused it) — graceful degradation is per declaration, not per file.                                                                                                                                                                                                                                                                                                                                                                                  |
| `Prove.lean`   | `#thales_prove` elaboration: `elabProp` builds the `Prop` (bounded binders → nested `ballIco`, unbounded int/nat → plain `∀`s, `≡` → `TsM Int` equality, boolean islands → `= pure true`), then a three-rung ladder — decide for all-bounded domains, simp/omega, grind on the residual — kernel-checks every proof via `addDecl`. The rungs split the per-annotation `thales.heartbeats` budget (bounded: half to decide, a quarter to each later rung; unbounded: half each), each under its own heartbeat window, so an early blowout (elaborator- or kernel-side) falls through to the next rung instead of consuming the annotation. |
| `Verdict.lean` | `Identity` (the `[file, function, property]` triple shared with the refutation engine), `Szs` (the closed status set), `Verdict`, and the sentinel-framed single-line JSON emitter.                                                                                                                                                                                                                                                                                                                                                                                                                                                       |

## The verdict channel

Each `#thales_prove` prints exactly one line to stdout: `thales-verdict:` + compact JSON `{identity, szs, reason}`. Stdout is also Lean's diagnostic stream; only sentinel-framed lines are contract, everything else is forwarded as diagnostics.

Verdict meanings, as `Prove.lean` assigns them:

- `Theorem` — a rung of the ladder succeeded (decide, simp/omega, or grind); the proof was added to the environment, so it is kernel-checked, not just elaborated.
- `CounterSatisfiable` — `decide` established the property is false on its bounded domain, and the domain was searched for a concrete witness, shipped in the verdict's `counterexample` field (binder name → value; values outside the JS safe-integer range travel as decimal strings).
- `GaveUp` — the ladder exhausted; the reason carries the pretty-printed residual goal that stumped the prover (or, in rung 1, the false-on-domain diagnosis with no witness to ship — including when the witness search itself ran out of budget, since established falsity is never given back for the cost of illustrating it). A rung that blows the recursion limit (`maxRecDepth`) has failed, but the annotation has not: the ladder falls through to the next rung and the goal reported is whatever survived.
- `Inappropriate` — the function could not be modeled because of an unmapped TypeScript construct (opaque node), or the property mentions such a declaration.
- `Error` — the attempt failed for any other reason; the reason names the phase that failed — building the property, or searching for a proof — so neither is ever blamed for the other's failure.
- `NotTried` — no structured property was provided (the transcriber's degradation path).
- `Timeout` — the attempt exceeded the per-annotation heartbeat budget (`thales.heartbeats`, overridable per run via `LAKATOS_PROVE_HEARTBEATS` → `-Dweak.thales.heartbeats=N`); later annotations in the file still run, each with a fresh budget. A budget of 0 is not a budget: `maxHeartbeats 0` means unlimited, so the option floors at 1 and the frontend ignores `LAKATOS_PROVE_HEARTBEATS=0` rather than forwarding it.

The set lives in exactly two places, one per language: the `Szs` inductive in `Verdict.lean` and the `SZS_STATUSES` array in root `src/szs.ts`, whose `ProveStatus` is that array minus the refute-only `InputError`. The root suite pins the two against each other (`tests/verdict-contract.test.ts`), constructor names and wire spellings alike. Everything else — the envelope's check, the frontend's parser, the check scripts — derives from the TypeScript side, so a new status means one edit per language and nothing else.

A verdict must also explain itself: an empty `reason` is a contract violation, contained like any other malformed line.

## Tests and checks

- `Test/ThalesDsl/` — Lean unit tests (`lake build ThalesDslTest`; each file also runs in isolation via `lake env lean`).
- `frontend/tests/` — vitest unit tests for transcribe/artifacts/run (run from the repo root; `run.test.ts` uses the injectable spawn, no real Lean needed).
- `scripts/check-verdict-channel.js` — the verdict-line contract over the hand-written fixtures in `tests/fixtures/*.lean`.
- `scripts/check-transcriber.js` — end-to-end: transcribes `tests/fixtures/tracer.ts`, runs the artifact, asserts expected verdicts.
- Both read the channel through the _built_ frontend (`scripts/harness.js` loads it, so a root build is required): the sentinel, the parse, the verdict validation, and the lake invocation are production's, not a copy the scripts could drift from.
- Root `tests/e2e.test.ts` — the full CLI prove path, gated on `LAKATOS_PROVE_E2E=1` so local and CI coverage stay identical.

CI: `.github/workflows/thales.yml` runs lake build, the Lean tests, both check scripts, and the gated prove e2e. The root `lakatos.yml` covers the frontend's vitest suite as part of the root package.

`tests/conformance/` is the verdict-fixture corpus: `.ts` fixtures bucketed by the SZS status every annotation in them must receive, run end to end by the root `tests/verdict-corpus.test.ts` (gated like the prove e2e). Its README documents the bucket conventions.

## Conventions

- **`autoImplicit` is off** project-wide (`lakefile.lean`); bind all implicit/universe variables explicitly.
- **Failure containment over abortion.** A construct the engine can't handle degrades that declaration (opaque node → `failedExt`), that annotation (`NotTried`/`Inappropriate`), or that artifact (`FileFailure`) — never the whole run. New frontend features should preserve this.
- **One verdict line per `#thales_prove`, always** — even for failures the elaborator can see. The check scripts enforce ordering and framing. Annotations the transcriber deliberately emits no command for (unsupported ranges) never enter the verdict channel; the CLI reports them from the transcription's `untried` list.
- **The Lean library builds here; the frontend builds at the root.** This directory's npm package (`thales-dev`) exists only for the check scripts and its own prettier pin.

## Agent skills

### Issue tracker

Issues are tracked as GitHub Issues on `jessealama/lakatos` (the monorepo), via the `gh` CLI. See `docs/agents/issue-tracker.md`.

### Triage labels

The five default triage labels, used as-is (`needs-triage`, `needs-info`, `ready-for-agent`, `ready-for-human`, `wontfix`). See `docs/agents/triage-labels.md`.

### Domain docs

Single-context: `CONTEXT.md` in this directory and `docs/adr/`. See `docs/agents/domain.md`.
