# Lemma semantics

This document gives meaning to the constructs of `grammar.ebnf` and
specifies the non-`@ensures` blessed annotations. It is a skeleton being
filled in; sections marked TODO are not yet normative.

## Structure of this document

Every construct is specified in three parts:

- **Well-formedness** — scoping and attachment rules beyond the grammar
  (what the construct may bind or refer to, where the annotation may
  appear).
- **Truth conditions** — the declarative claim the construct makes, stated
  over the value space of its domains. One meaning, stated once. This
  section never mentions any engine.
- **Engine obligations** — what each kind of engine does with the claim: a
  *refuter* approximates truth by sampling (it can establish falsity, never
  truth); a *prover* establishes truth by translation into a proof
  assistant (it can establish truth, and reports counterexamples as
  falsity). If this document ever specifies the behavior of a particular
  tool (fast-check, Lean), that is a bug in this document.

## Blessed annotations

| Annotation | Grammar | Refutable | Provable |
|---|---|---|---|
| `@ensures{name} <property>` | `property` in `grammar.ebnf` | yes | yes |
| `@throws` | marker (TODO: optional type list) | yes (run it, check it throws) | yes |
| `@total` | marker | no (termination is not observable by sampling) | yes |

## `@ensures` properties

### The property as a whole

- **Well-formedness**: attaches to an exported function declaration. Binder
  names are pairwise distinct and scope over the formula body. TODO:
  attachment to other declaration forms.
- **Truth conditions**: the formula holds for every assignment of values to
  the bound variables drawn from their (guarded) domains.
- **Engine obligations**: the refuter samples assignments and evaluates;
  the prover quantifies universally over the (guarded) domain's
  translation. The prover's coverage is bounded `int`/`nat` binders: it
  establishes a property by evaluating it over the whole domain, so a
  domain it cannot enumerate is reported unproven rather than assumed.

### Binder domains

`int`, `nat`, `number`, `boolean`, `string`, `bigint`.

- **Truth conditions**: `int`/`nat` denote the mathematical (unbounded)
  integers/naturals; `number` denotes IEEE-754 binary64 and ranges over
  every value a TypeScript `number` can take, `NaN`, `±∞` and `±0`
  included. An interval guard on a `number` binder excludes `NaN` — which
  satisfies no interval — and clips the infinities to the interval: an
  infinite endpoint written open (`(-∞,` or `, ∞)`) excludes the infinity
  of that sign, while one written closed (`[-∞,` or `, ∞]`) includes it.
  Because a binder's value is passed to a `number`-typed parameter, an
  `int`/`nat` binder's values must be exactly representable as binary64;
  values outside `±(2^53 − 1)` are not, which is why an interval reaching
  beyond that range is refused rather than narrowed.

### Guards (`∈` constraints)

- **Truth conditions**: an interval guard restricts the domain to the
  denoted (half-)open interval; a regex guard restricts `string` to exactly
  the whole-string language of the pattern (auto-anchored `^(?:…)$`).
- **Engine obligations**: TODO — the refuter must sample only guarded
  values (not sample-and-discard); the prover carries the guard as a
  hypothesis. Where the two cannot denote the same set, the prover's must
  be the larger: it may then fail to prove what the refuter cannot falsify,
  but it can never establish a property the refuter can refute. A `number`
  interval excludes an endpoint by adjacency, in an ordering where -0 sits
  strictly below 0; IEEE comparison cannot separate the two zeros, so a
  bound excluding one of them is carried in its closed form rather than
  silently excluding the other as well. On the special values the engines
  must agree exactly, since a property can hold on every finite double yet
  fail at an infinity or `NaN`: an infinite endpoint is carried as a
  comparison against that literal infinity — strict when open, non-strict
  when closed, either of which IEEE comparison refuses for `NaN` — so any
  interval denotes a `NaN`-free set to both engines, and only a binder
  with no interval at all ranges over the whole domain, `NaN` included.

### Connectives

- **Truth conditions**: classical two-valued semantics over
  boolean-valued atoms; precedence and associativity per the grammar.
- **Root implication vs. parenthesized implication** — a real semantic
  distinction, not sugar: at the formula root, `P ==> Q` is a
  *precondition* — assignments falsifying `P` are outside the claim
  (the refuter discards the sample; the prover takes `P` as a
  hypothesis). A parenthesized `(P → Q)` is ordinary material
  implication, `¬P ∨ Q`. The two coincide for truth conditions at the
  root but differ in what an engine reports about vacuity; TODO: state
  the vacuity-reporting obligation (e.g. a refuter should report when
  all samples were discarded).

### Equations (`≡` / `≢`)

- **Truth conditions**: `A ≡ B` holds iff `A` and `B` are the same value
  in the sense of SameValue (`Object.is`): no coercion, `NaN ≡ NaN`,
  `+0 ≢ -0`.
- **Engine obligations**: `≡` is SameValue and `≢` its negation. The
  refuter compares with `Object.is`. The prover compares binary64 values
  for bit-level identity, which coincides with SameValue except that it
  distinguishes `NaN` payloads where `Object.is` does not — so the prover
  may decline to prove a true claim about distinct `NaN` payloads, but it
  can never prove a false one. Strict equality (`===`) is a distinct
  relation: IEEE, in which `NaN` differs from itself and `+0` equals `-0`.

### Islands (host expressions)

- **Well-formedness**: an island is an opaque expression of the host
  language (TypeScript). This specification defers island *syntax*
  entirely to the host; it constrains what islands may *do*:
  - must evaluate to a genuine boolean (in atom position);
  - must be pure: no assignments, no observable side effects;
  - free identifiers must be exported from the annotated module.
- **Truth conditions**: the value of the expression under the host
  language's semantics, with binders bound to the assignment under test.
- **Engine obligations**: the refuter evaluates islands natively; the
  prover translates islands into its logic and must state, in its verdict,
  any island it instead treated as opaque (an assumption, not a proof —
  see trust reporting below). TODO: the admissible-island subset for
  provers.

## `@throws`

TODO. Sketch of the intended contract: the annotated function throws on
every input (or on the inputs satisfying a stated precondition). Refuter
obligation: run and confirm a throw occurs. Prover obligation: prove the
translation reaches a throwing state. Messages and exception classes are
not part of the claim (throw-iff, relaxed).

## `@total`

TODO. The annotated function terminates on every input. Prover-only: the
prover discharges termination of the translation; a refuter cannot
establish or refute termination by sampling and must report the
annotation as out of scope.

## Verdicts and SZS statuses

Engines and frontends report per-property verdicts. The human-facing word
leads; the machine-facing status is drawn from the
[SZS ontology](https://tptp.org/UserDocs/SZSOntology/) and appears as
metadata (detail lines, JSON `status` fields) — never as process exit
codes.

| Verdict (human) | SZS status | Meaning |
|---|---|---|
| PROVED | `Theorem` | Established for all inputs (exhaustive check or proof). Assumptions (opaque islands, assumed callee contracts) must be listed with the verdict. |
| REFUTED | `CounterSatisfiable` | A concrete counterexample exists (and is reported). |
| TESTED, not proved | `Unknown` | No engine established the claim; sub-statuses per engine (e.g. refuter `GaveUp` after its budget with no counterexample, prover `GaveUp`). |
| UNSUPPORTED | `Inappropriate` | The code the annotation depends on is outside the engine's mappable subset — the claim was never evaluated, which is a statement about the engine, not the property. The verdict carries a reason naming the offending construct. |
| — | `Timeout` | An engine exhausted its budget. |
| — | `InputError` / `SyntaxError` / `TypeError` | The annotation or the annotated code is malformed. |

TODO: the exact sub-status composition rules for frontends aggregating two
engines' reports.
