# Thales-TS Growth Path

This is the canonical statement of where Thales is going; when
direction changes, this document changes with it. It was last reset in
August 2026, replacing the earlier "two story arcs" framing (meet
TypeScript halfway / bring proofs to TypeScript) with a single
destination that subsumes both.

## The destination: proof as property-based testing's endgame

Property-based testing lets TypeScript programmers state properties of
their functions in JSDoc and tries to refute them with generated
inputs. The limit of that method is built in: failing to refute a
property — even across many runs — is evidence, not proof.

Thales is the tool that crosses that limit: the same annotation the
user already wrote for testing gets escalated, where possible, to a
machine-checked claim about **all** inputs. One spec, strongest
available guarantee:

> You wrote a property. Ten thousand generated inputs failed to refute
> it. Thales proved it for every input there is.

Thales is one engine in a small constellation, each part with one job:

- [lakatos](https://github.com/jessealama/lakatos) is the user-facing
  frontend. Its flagship command, `lakatos check`, runs the
  proofs-and-refutations loop: try to refute, then try to prove,
  report the strongest verdict earned.
- [pabst](../../pabst/) is the refutation engine: properties become
  fast-check runs hunting for counterexamples.
- Thales is the proof engine.
- [Lemma](../../../spec/) is the specification language the other
  three share (see "The spec dialect" below).

The dependency arrows point one way: lakatos depends on both engines,
the way Vite depends on esbuild or Prisma depends on its query
engines; the engines never depend on each other. Thales never invokes
pabst. All three live in one repository — the lakatos monorepo — as
components of one product, cut from the same commit with one version
number; Thales remains usable directly by anyone who wants the
engine without the frontend.

## The verdict ladder

Specs are checked automatically on every run, like types. There is no
"promote to proved" annotation and no manual proof syntax. For each
`@ensures`, Thales attempts, in order:

1. **Exhaustive check.** When the quantified domain is bounded —
   `Byte`, `Bit`, bounded integer ranges, small finite ADTs — the
   property is checked by evaluation over the entire domain. This is a
   genuine for-all claim, and it needs no tactic sophistication at
   all.
2. **Proof.** A fixed, curated tactic stack attempts a general proof.
   We expect this to succeed on a characterized class — quantifier-free
   arithmetic, structural recursion over algebraic data — and we widen
   that class deliberately, not speculatively.
3. **Neither.** Thales reports "unable to prove" as a non-fatal
   diagnostic. The spec is not an error and nothing is blocked; under
   `lakatos check` the property simply retains its tested status.

A counterexample discovered at any rung is always an error. Tactic
weakness degrades a verdict; it never punishes the user.

Verdicts carry [SZS ontology](https://tptp.org/UserDocs/SZSOntology/)
statuses as machine-readable metadata — `Theorem` for a proved
property, `CounterSatisfiable` for a refuted one, `Unknown` with a
`GaveUp` sub-status when the ladder is exhausted — shared vocabulary
across Thales, pabst, and lakatos output. Exit codes stay boring and
Unix-shaped; the ontology lives in output and JSON, never in exit
codes.

## The unit of verification

The unit is the annotated function plus its transitive callees — not
the file, and not the project. Code outside that cone is invisible:
classes, mutation, and async elsewhere in the module must not block
verifying a pure annotated function. This reframes subset coverage
from "handle real-world TypeScript" (unbounded) to "handle what people
write inside pure algorithmic kernels" (tractable, and largely what
the subset already is).

When the cone does escape the subset — a stdlib gap, an out-of-subset
helper, an npm import — the callee becomes an opaque constant typed
from its TypeScript signature, with its own `@ensures` (if any) taken
as assumptions. The verdict then says so, explicitly:

```
PROVED, assuming:
  _.chunk matches its declared signature
  parseDate satisfies its @ensures
```

The assumption list is a feature, not an apology: it is the worklist
of what to verify next, and the report format must make the trust
boundary impossible to miss.

Today Thales compiles whole files; cone-based verification is planned
work, sequenced below.

## The spec dialect

The dialect is [Lemma](../../../spec/): `@ensures{name}` with
`forall` binders and `==>`, living entirely inside JSDoc, so
`tsc --strict` and the rest of the ecosystem see ordinary TypeScript.
The grammar was developed in pabst and now has a
neutral normative home — an engine cannot own the shared surface —
along with prose semantics and a conformance-fixture corpus. Thales's
annotation parser is held to that corpus; the two engines are two
discharge modes for one spec language. The Lemma grammar stops at the
annotation boundary: formula structure is Lemma, the leaves are
opaque TypeScript expressions, and Thales's accepted subset of
TypeScript itself remains specified operationally by this
repository's conformance corpus, not by any grammar.

## Distribution

No TypeScript programmer will install a Lean toolchain by hand, and
none will be asked to. The monorepo's releases include prebuilt
per-platform engine bundles — the compiler binary plus the pinned
toolchain and compiled runtime — cut from the same commit as the
frontend (one version number, no pin to bump), and lakatos downloads
the bundle on first use, the way Playwright fetches browsers. The
words "elan" and "lake" never appear in a user's terminal. A
first-class GitHub Action caches the same bundle so CI proving is a
few lines of workflow.

The latency bar for the check loop is seconds, not minutes: a file
with a handful of specs should return its verdicts fast enough to run
on save. If shelling out to the toolchain threatens that bar, the
scoped fix is elaborating the emitted module in-process — Thales is
itself a Lean program — as a performance task, not a change of
direction.

## What today's engine already provides

The guarantees that ship today fold directly into this story:
`@total` (Lean-checked termination, no escaping failure), `@throws`
(failure modes in the signature), and the bounded numeric types with
their compile-time range checking. They are the floor the verdict
ladder stands on.

The byte-identical conformance contract — emitted Lean must reproduce
the program's stdout, stderr, and exit code exactly — is hereby
reclassified as what it always was: translation validation. It is the
internal soundness infrastructure that makes a PROVED verdict mean
something about the original TypeScript, not a user-facing feature.
It stays, and it stays strict.

Subset widening continues, but demand-driven: constructs are admitted
because verification targets need them, not to chase coverage for its
own sake. The Decimal
([#126](https://github.com/jessealama/thales/issues/126)) and Amount
([#130](https://github.com/jessealama/thales/issues/130)) polyfill
ports (issues on the pre-monorepo thales tracker) are repositioned
from widening capstones to showcase corpus for
the ladder — real, spec-bearing code the verdict ladder should
eventually run on end-to-end.

## Sequencing

1. **Tracer bullet.** One `@ensures` on one pure, in-subset function;
   the full ladder end-to-end (exhaustive check, tactic stack, honest
   "unable to prove"); graded verdict printed. Whole-file subset as
   today; no cone analysis; no pabst wiring. This is the experiment
   that validates the direction cheaply — if the ladder cannot produce
   PROVED on honest hand-picked examples, that is learned in weeks.
2. **Latency.** Measure the pipeline on a decide-dischargeable spec;
   in-process elaboration if the on-save bar is missed.
3. **Cone-based verification.** The annotated-function unit, opaque
   callees, and the trust report.
4. **Distribution.** Prebuilt bundles, the auto-download path, the
   GitHub Action, and the lakatos glue.

## Emit architecture: structured output instead of strings

A robustness follow-on, unchanged by the reset. The emitter builds
Lean source by rendering a custom `LExpr` AST to strings;
parenthesization and layout are hand-maintained invariants, and that
class of invariant has leaked twice (an orphaned `else` in a nested
do-block; a missing `.some` injection into an `Option`-typed slot).
Two remedies remain on the shelf: build `Lean.Syntax` and serialize
through Lean's own parenthesizer and formatter, or keep `LExpr` and
replace the renderer with a `Std.Format`-based, precedence-aware one.
The trigger to pick this up is a third instance of the bug class or an
emit expansion that multiplies the layout-sensitive contexts we
maintain by hand — and the in-process elaboration work in the
sequencing above naturally revisits this choice.

## Non-goals

- **All of TypeScript.** Thales will never accept everything
  `tsc --strict` accepts. The goal is Lean-backed verification for a
  disciplined subset, not fidelity to the whole language.
- **Executing user programs.** Node runs TypeScript; Thales does not
  and will not. The earlier idea of embedding a JS runtime so that
  `thales foo.ts` elaborates and executes the program is explicitly
  rejected: execution of emitted Lean serves translation validation
  internally, and no user problem calls for more.
- **Decorators and mixins.** Both remain hard to model faithfully in
  Lean and are not near-term work.

This list isn't written in stone. As Lean grows, and as our knowledge
of Lean and TypeScript grows, items may move off it — or onto it.
