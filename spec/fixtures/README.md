# Lemma conformance fixtures

Three corpora, each with its own scope and its own harness. **Directory
membership is the expectation** in all of them: every implementation must
accept everything under `accept/` and reject everything under `reject/`.
None has an `expect` field.

- `accept/`, `reject/` — **property bodies**. Constrain the parser: what
  a well-formed `@ensures` formula looks like.
- `attach/accept/`, `attach/reject/` — **attachment points**. Constrain
  extraction: which declarations an `@ensures` may be attached to, per
  *Attachment points* in `../semantics.md`.
- `binder/accept/`, `binder/reject/` — **class-valued binder domains**.
  Constrain binder validation: which classes a binder may range over, per
  *Class-valued binders* in `../semantics.md`.

## Property-body fixtures (`accept/`, `reject/`)

Each fixture is one JSON file holding a single `@ensures` property body (the
text after the `@ensures{name}` tag). **Directory membership is the
expectation**: every implementation must accept everything under `accept/`
and reject everything under `reject/`. There is no `expect` field.

Fixture shape:

```json
{
  "annotation": "forall (x y: int) { x + y === y + x }",
  "note": "what this fixture locks in",
  "stage": "prefix | formula"
}
```

`stage` appears only on reject fixtures and is informative, not normative:
it records which part of the reference parser rejects the input (the
quantifier prefix or the formula body). Implementations must reject the
whole annotation; they need not fail at the same stage.

These are surface-syntax fixtures only: they constrain parsing, not typing
or evaluation. Validation-stage rules that need the enclosing module (e.g.
"free identifiers must be exported") are out of scope here.

Provenance: the seed corpus was verified against the reference
implementation (pabst's shipped parser) before being committed.

Planned: a `tree` field per accept fixture giving the golden parse tree as
JSON, once the canonical AST shape is settled; until then, accept fixtures
assert acceptance only.

## Attachment fixtures (`attach/accept/`, `attach/reject/`)

Each fixture is one TypeScript module carrying exactly one `@ensures`. The
module is what a property-body fixture cannot be: whole enough to say
whether the annotated declaration is exported, public, and of a kind that
can bear a property.

An `attach/accept/` module must yield exactly one extracted annotation and
no diagnostic. An `attach/reject/` module must yield exactly one diagnostic
and no annotation — a rejected attachment is reported, never dropped in
silence.

The formulas are deliberately dull. What a fixture pins is the attachment
point, so a formula that failed to parse would move the failure to the
wrong stage; the property-body corpus above is where formula syntax lives.

## Binder-domain fixtures (`binder/accept/`, `binder/reject/`)

Each fixture is one TypeScript module carrying exactly one `@ensures`
whose quantifier prefix contains a class-valued binder. Like attachment,
class-name resolution is context-sensitive: only a whole module can say
whether the name denotes an exported, non-default class declared there,
and whether that class's constructor parameters are generable.

A `binder/accept/` module must yield exactly one annotation whose prefix
parses and validates with no diagnostic. A `binder/reject/` module must
yield exactly one diagnostic naming the offending domain or constructor
parameter — a rejected binder is reported, never dropped in silence.

The classes and formulas are deliberately dull, and every attachment
point is unremarkable: what a fixture here pins is the binder's
eligibility alone. Parse-level facts about class domains (e.g. that a
class domain admits no `∈` constraint) stay in the property-body corpus.

This corpus is committed ahead of the reference implementation of
class-valued binders; its harness lands with that implementation.
