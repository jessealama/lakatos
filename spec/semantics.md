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

- **Well-formedness**: attaches to one of the declaration forms listed
  under *Attachment points* below. Binder names are pairwise distinct and
  scope over the formula body.
- **Truth conditions**: the formula holds for every assignment of values to
  the bound variables drawn from their (guarded) domains.
- **Engine obligations**: the refuter samples assignments and evaluates;
  the prover quantifies universally over the (guarded) domain's
  translation. The prover establishes a property only where its methods
  genuinely reach — exhaustive evaluation over a domain it can enumerate,
  or symbolic proof over one it cannot — and a claim it cannot settle is
  reported unproven, never assumed.

### Attachment points

An `@ensures` names the declaration it is attached to. That declaration
must be reachable from outside its module, since a property no caller can
exercise is not a property of the module's interface. Every accepted form
yields a *qualified name*, the second component of a verdict's identity
triple (file, qualified name, property name):

| Attachment point | Qualified name |
|---|---|
| Exported function declaration | `f` |
| Exported `const` bound to an arrow or function expression | `f` |
| Public instance method of an exported class | `C#m` |
| Public static method of an exported class | `C.m` |
| Public instance getter of an exported class | `C#g` |
| Public static getter of an exported class | `C.g` |
| Constructor of an exported class | `C#constructor` |

A class's members share one namespace, so no two accepted attachment
points on a class can collide: a class has at most one constructor, and a
getter and a method cannot share a name.

These are not attachment points:

- **Setters.** A setter's call has no value, so there is nothing for a
  formula to speak about.
- **Abstract members.** They have no body to check a claim against.
- **Computed-name members** (`[Symbol.iterator]`, `["x"]`). The name has no
  fixed spelling, so the identity triple cannot name the subject.
- **Fields**, including a field initialized with a function expression. A
  field is reassignable, so the annotation would not pin the callee.
- **Non-public members** — `private`, `protected`, or `#private`, the
  constructor included. No caller outside the class can reach them.
- **Members of a non-exported class**, and **members of an anonymous
  class**: unreachable, and unnameable, respectively.

A rejected attachment is a diagnostic, not silence: the annotation is
reported with the best identity available, which may use the placeholder
labels `<computed>` and `<anonymous>`.

An `@ensures` lives in a JSDoc block (`/** ... */`) directly above its
declaration. Every block stacked there contributes its `@ensures` tags, in
source order: one property per block and several properties per block are
the same annotations. TypeScript's own JSDoc accessors read only the last
block; Lemma reads them all, because an annotation dropped in silence is the
one outcome a checker must not have.

### Binder domains

`int`, `nat`, `number`, `boolean`, `string`, `bigint`, or a class name
(see *Class-valued binders* below).

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

### Class-valued binders

A domain may be a class name: `∀ (p q : Point) { 0 <= p.distance(q) }`.

- **Well-formedness**: the name resolves to an exported, non-default,
  named class declared in the annotated module — the same reachability
  rule attachment points and island free identifiers follow. An imported
  class is not yet an admissible domain. The six primitive domain
  spellings are reserved and shadow any class of the same name. A class
  domain admits no `∈` constraint. Every constructor parameter must be
  annotated with one of `number`, `boolean`, `string`, or `bigint`, or
  with a class that is itself admissible as a binder domain in the same
  module; union, optional, and rest parameters are refused, with a
  diagnostic naming the parameter. The constructor-parameter graph over
  the module's classes must be acyclic: a cycle — direct or mutual —
  has no base case and so no image to quantify over, and is refused
  with a diagnostic naming the cycle. A parameter default is admitted:
  quantification is at full arity, every argument supplied, and since a
  default inhabits its own parameter's declared type, every instance a
  defaulted call can reach is already reached at full arity.
- **Truth conditions**: the binder ranges over the *image of successful
  construction*: the property holds iff, for every tuple of argument
  values drawn from the constructor's parameter domains on which
  construction completes normally, the formula holds of the instance the
  constructor returns. The constructor's guards thereby define the
  domain — an argument tuple on which construction throws denotes no
  instance and lies outside the quantifier — and whatever normalization
  the constructor performs is part of the domain, because the binder
  denotes the constructor's outputs, never its raw inputs. A binder
  group `(p q : C)` is two independent quantifications over the same
  image, exactly as with primitive domains.

  A class-typed constructor parameter is read the same way, one level
  down: its domain is the image of *its* class's construction, so the
  domain expands recursively, innermost first, until it bottoms out in
  primitives. Acyclicity guarantees it bottoms out. A tuple of primitive
  values on which any inner construction throws denotes no inner
  instance, hence no outer one, and lies outside the quantifier —
  exactly the reading a single level has, applied at each level.

  The claim is about constructed, unmutated, exact instances. Three
  families of values TypeScript's type system would call `C` are
  explicitly outside it: structurally-typed values that never passed
  through the constructor (object literals, casts), instances of
  subclasses, and instances mutated after construction (including
  through `readonly`, which is erased at runtime). A fourth lies outside
  it for the same reason defaults are admitted: a constructor that
  observes its own arity (through `arguments.length` or its kin) can
  make a defaulted call construct an instance no full-arity call
  produces, and such instances are outside the claim. An always-throwing
  constructor yields an empty domain, over which every property holds
  vacuously — the same situation as an interval guard denoting the
  empty set.
- **Engine obligations**: the refuter draws argument tuples from the
  constructor's parameter domains, runs the real constructor, and
  discards any tuple on which construction throws — the same discard
  channel as a failing root-level antecedent. Where a parameter is
  class-typed, the values drawn are the innermost primitives and the
  real constructors run outward, a throw at any level discarding the
  whole tuple through that same channel; discard rates multiply with
  depth, so exhausting the discard budget is likelier the deeper the
  nesting. It must not derive its sampling from the guards' text, only
  from the parameter types: a refuter that pre-filters by reading the
  guards can never catch a defective guard. A constructor invocation in
  the *formula body* enjoys no such reading — there it is an ordinary
  island call, and a throw is a counterexample. A refuted property's
  counterexample reports the constructor argument tuples — nested,
  where a parameter is class-typed — the reproducible identity of an
  instance. The prover quantifies over every tuple in the parameter
  domains — for `number`, all of binary64, `NaN` and the infinities
  included, exactly as an unguarded binder — and takes "construction
  completed normally, with this result" as its hypothesis, one such
  hypothesis per level of nesting, each level's in scope for the levels
  outside it; the constructor's guards, not free hypotheses, are what
  restrict the domain, so weakening a guard genuinely weakens what the
  annotation claims. The engines therefore agree on the domain — the
  image — and differ only in how they explore it: a refuter sampling
  policy that omits a value on which the constructor always throws
  leaves no image value uncovered.

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
