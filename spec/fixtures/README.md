# Lemma conformance fixtures

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
