# Class-valued binders — design

Date: 2026-08-25. Grilled with Jesse to completion (all branches resolved).
Driver: the TC39 TG5 talk's `Point.mts` example, whose annotation is the
target surface:

```ts
export class Point {
  public readonly x: number;
  public readonly y: number;

  constructor(x: number, y: number) {
    if (
      x === -Infinity ||
      x === Infinity ||
      y === -Infinity ||
      y === Infinity
    ) {
      throw new RangeError("Cannot accept infinite coordinates");
    }
    if (Object.is(x, NaN) || Object.is(y, NaN)) {
      throw new RangeError("Coordinates cannot be NaN");
    }
    if (Object.is(x, -0)) {
      x = 0;
    }
    if (Object.is(y, -0)) {
      y = 0;
    }
    this.x = x;
    this.y = y;
  }

  /**
   * @ensures{nonNegative} ∀ (p q : Point) { 0 <= p.distance(q) }
   */
  distance(p: Point): number {
    const dx = p.x - this.x;
    const dy = p.y - this.y;
    return Math.sqrt(dx * dx + dy * dy);
  }
}
```

Verified baseline (2026-08-25, both engines at main):

- `lakatos refute Point.mts` → exit 2,
  `unknown generation domain 'Point' — valid domains: int, nat, number,
boolean, string, bigint` (lemma `prefix-parser.ts:218`).
- `lakatos prove Point.mts` → `Inappropriate`, `unmapped TypeScript
construct 'ClassDeclaration'` (the transcriber refuses the class before
  the binder domain is ever consulted).

## D1. Scope: Lemma + pabst now; thales post-parity

The plain-Lean emission freeze (epic #144) holds: no new thales language
features until emission parity. This work lands in three tiers:

1. **Now**: grammar + `semantics.md` + conformance fixtures; lemma parse
   and validation; pabst generation. `lakatos refute` handles the
   annotation as written by talk time.
2. **Now, minimal**: the frozen thales pipeline reports `Inappropriate`
   for class binders (containment, not support), with a parity twin filed
   per the freeze rule.
3. **Post-parity**: `Point#distance` to `Theorem`, as the natural tracer
   rung of the planned thin-classes epic (before `offsetMonotone`, which
   stays the prize).

Racing class support onto the dying `ts.` DSL was considered and
rejected: throwaway work and the freeze's first violation a day after it
was set. The talk is a live research demo; `refute` succeeding and
`prove` declining _with a reason it can name_ is the honest slide.

## D2. Semantics: the binder ranges over the constructor's image

`∀ (p : C) { φ(p) }` holds iff for every argument tuple in the
constructor's parameter domains on which `new C(...)` returns normally,
φ holds of the returned instance.

- The domain is the **image of successful construction** — the guards
  in the constructor _define_ the domain; a throwing tuple denotes no
  instance and is outside the quantifier. The `-0` normalization comes
  out right for free: the image contains normalized points, not raw
  argument pairs.
- Documented **non-claims** (`semantics.md` names these explicitly):
  structural impostors (TS's structural typing admits object literals
  and `as any` cheats that never met the guards), subclasses, and
  runtime mutation through erased `readonly`.
- `readonly` fields are **encouraged** (they make the ctor-image reading
  true in TS's own terms, and preview the eventual Lean structure
  immutability) but **not required** for binder eligibility — the
  refuter never mutates, and requiring it would reject real classes for
  a property the checker can't exercise.
- Always-throwing constructor ⇒ empty domain ⇒ vacuous truth (prover)
  vs. discard-exhausted `GaveUp` (refuter). Logically correct, same as
  an empty primitive interval; documented, not worried about.

## D3. Grammar and resolution

`domain ::= "int" | "nat" | "number" | "boolean" | "string" | "bigint"
| class-name`, where `class-name ::= IDENT` with validation side
conditions:

1. Resolves to an **exported class declared in the annotated module**
   (same rule as attachment points and island free identifiers).
   Imported classes as domains: deferred. The six primitive keywords
   stay reserved; a class literally named `number` is unaddressable
   (teaching error if detectable).
2. **No constraints**: `(p : Point ∈ …)` is a parse-time teaching error;
   the `∈ guard` production stays numeric/string-only.
3. Anonymous and default-export classes rejected (no fixed spelling for
   the identity), mirroring attachment rules.
4. **Generability side condition** (parse/validation-time, like the
   regex-generator check): every constructor parameter must have a plain
   generable type annotation — one of `number | boolean | string |
bigint`. No class-typed params, unions, optionals, or rest in v1 (each
   loosening is a one-way door; start strict); defaults (D9, #221) and
   acyclic class-typed params (D9, #220) were since admitted.

Parse cases live in the body-syntax JSON corpus (`spec/fixtures/*.json`);
resolution/eligibility cases are context-sensitive and live in the
whole-module corpus (`spec/fixtures/attach/`-style).

## D4. Refuter obligation (pabst)

For each class binder, draw one argument tuple per the ctor's parameter
types using the **existing per-domain arbitraries** (so `number` params
get the standard noNaN double generator, infinities included), then run
the **real constructor**:

- Ctor throw during binder materialization = **discard** (same channel
  as a failing root-level antecedent). Discard exhaustion behaves like
  the guard-chain case (#90): `GaveUp` on heavily-discarding true
  properties is expected.
- Sharp distinction preserved: a `new C(...)` _in the formula body_ that
  throws is still a refutation (`kind: "threw"`). Binder position is
  what moves ctor guards from obligation to domain definition.
- **No guard-aware biasing** (e.g. `noDefaultInfinity` to cut discards):
  pabst executes the constructor, never analyzes it — pre-filtering by
  peeking at guards would make guard bugs unfindable.
- Counterexamples report the **argument tuples** (`p: new Point(0, 5)`
  style), the reproducible serializable identity of an instance.
- Generated-spec **import derivation must include binder-domain
  classes** — the class name may never appear in the formula text.
- NaN never generated for ctor args (existing noNaN policy) — a search
  choice, not a semantic one: NaN tuples throw, so nothing in the image
  is reachable only via NaN args.

## D5. Prover obligation (thales, post-parity)

Engine-neutral contract in `semantics.md` now; Lean shape later:

```
∀ (x1 y1 : JsNumber), ∀ p, Point.construct x1 y1 = .ok p → φ p
```

- `p` is the constructor's **output**, never `Point.mk` of the raw args
  — the hypothesis routes through the emitted ctor in `JsM`, so `-0`
  normalization is part of the domain automatically.
- Args quantify over the **full TS parameter type** (all Floats, NaN and
  ±∞ included), with no free finiteness hypotheses: the guards do the
  restricting. Deleting a guard genuinely changes the obligation. The
  engines agree on the domain (the image) and differ only in
  exploration.
- `p.distance(q)` — member call with a class-binder receiver — maps to
  the emitted method def, receiver as first argument. Other island uses
  of binder values flow through existing degrade-to-`Inappropriate`
  containment.
- `(p q : C)` = two independent image-quantifications, like primitive
  binder groups.

## D6. The body: verified spec facts

- **`Math.sqrt` is exactly specified** in ECMA-262: absent from the
  "not precisely specified" list (which names `pow`, `hypot`, `exp`,
  the trig family), algorithm ends `Return 𝔽(the square root of ℝ(n))`
  — correctly rounded. Lean v4.33 `Float.sqrt` is kernel-reducible via
  `Float.Model`. Soundly modelable, no axioms; becomes the first
  modeled `Math.*` builtin (#88 family), post-parity.
- **`Math.pow` is doubly refused**: in the spec's imprecise list (same
  ground as `**`, #98) _and_ `Float.pow` is opaque in Lean. Never map
  it. The example's body was rewritten (`dx * dx`) — better JS anyway,
  since `x * x` is exact IEEE while `pow(x, 2)` is spec-licensed to
  approximate.
- **`Object.is` is load-bearing for Point** (ctor uses it twice) and has
  no model today. It is SameValue — exactly specified, kernel-computable
  over floats via bit comparison. Joins `Math.sqrt` on the builtin list.
- FloatFacts needed for the Theorem: square-nonneg (x non-NaN →
  `0 ≤ x*x`, covering ±∞ overflow), nonneg+nonneg stays nonneg and
  non-NaN, sqrt-nonneg on non-NaN nonneg. All provable from
  `Float.Model`, same layer as the four monotonicity facts. Field
  finiteness arrives as hypotheses from the ctor-succeeds desugaring —
  the guards Jesse wrote are literally the hypotheses the proof needs.

## D7. Freeze-window prove behavior

The old transcriber gets one explicit case: class binder → no
`#thales_prove` command, verdict `Inappropriate`, reason naming the
construct ("class-valued binder 'Point' is not yet modeled"). This
pre-implements the new architecture's frontend-classifies rule, and
files its twin parity issue per the freeze discipline: the new emitter
classifies class binders identically until the thin-class epic models
them.

Demo symmetry this buys: the same annotation gets `refute → GaveUp`
after a real search and `prove → Inappropriate` naming exactly the
construct the research is about.

## D8. Packaging

Filed as GitHub issues (dependency edges native):

1. Spec: grammar + `semantics.md` class-binder contract + conformance
   fixtures (body-syntax parse cases; whole-module resolution cases).
2. Lemma + pabst implementation (blocked by 1).
3. Thales freeze-window containment, D7 (blocked by 1).
4. Post-parity: `Point#distance` to `Theorem` (blocked by #152) —
   carries the D5/D6 ingredient list; adopted as the thin-class epic's
   tracer rung when that epic is designed. Thin-class epic itself NOT
   filed now (deserves its own design pass; #144 reserved the slot).
5. Parity twin of 3 on the new pipeline (sub-issue of #144, blocked
   by 3).

Talk logistics (not an issue): the presentation directory must be an
npm project with `lakatos`, `vitest`, `@fast-check/vitest` installed
for the live refute demo.

## D9. Constructor-shape extensions (grilled 2026-08-27)

D3.4 bans class-typed params, unions, optionals, defaults and rest as a
v1 one-way-door policy. A second grilling took each in turn; the domain
semantics of D2 are unchanged by all of it.

- **Image reading reaffirmed.** Quantifying over a class binder is
  quantifying over its constructor's arguments, but a tuple on which the
  constructor throws is _outside_ the quantifier, not a counterexample.
  A direct-substitution reading (`phi(new Point(x, y))`) would make a
  throwing tuple refute, erasing D4's distinction between binder
  position and formula-body position. Filed nowhere: this is D2 as
  already written.

- **Class-typed params: allowed when acyclic** (#220, blocked by #219).
  Expansion nests innermost-first, each level's ctor-succeeds hypothesis
  in scope for the next, bottoming out in primitives. A cycle in the
  constructor-parameter graph has no base case and is a validation-time
  teaching error, so no depth bound is needed. Refuter discards compound
  with depth.

- **Defaults: allowed, no domain change** (#221). Full-arity
  quantification subsumes defaulted calls, since a default inhabits its
  own parameter's declared type. New non-claim: a constructor branching
  on `arguments.length`.

- **Optionals, unions, rest: stay banned** (#222, blocked by #127 and
  #131). Each needs a value the domain lacks — `undefined`, a tagged
  union, arrays — so none is a class-binder problem.

- **Statics are not domain contributors** (#223, docs only). A factory
  that delegates to the constructor has an image that is a subset of the
  ctor image, so it adds nothing; a private constructor makes the ctor
  image an over-approximation, which is a documented non-claim rather
  than a reason to make the domain a disjunction over entry points. TS
  accessibility is erased at runtime, so it cannot carry semantic
  weight — the same ground as the structural-impostor non-claim.
