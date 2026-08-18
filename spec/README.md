# Lemma

A little specification language for TypeScript, embedded in JSDoc.

Lemma is how you state properties of your functions — universally
quantified claims over their inputs — without leaving TypeScript:

```ts
/**
 * @ensures{nonzero} forall (x: bigint) (y: number) {
 *   Number.isInteger(y) ==> foo(x, y) !== 0
 * }
 */
export function foo(x: bigint, y: number): number {
  return Number(x % 2n) + (y % 2) + 1;
}
```

The annotations live in JSDoc comments, so every annotated file remains an
ordinary TypeScript file accepted by `tsc --strict`. Formula structure
(quantifier prefix, connectives, equations) is Lemma; the leaves are opaque
TypeScript expressions — Lemma specifies the boundary, not the interior of
the host language.

## What this directory is

The home of the Lemma language, independent of either engine in this
repository. It is scaffolding for those engines, not a standards play: a
standalone spec repository gets extracted only when a second independent
implementation exists or a standards venue asks for a normative reference
— not before.

- **`grammar.ebnf`** — the surface syntax of `@ensures` property bodies.
  The single source of truth for the dialect.
- **`semantics.md`** — well-formedness rules, truth conditions, and the
  obligations each kind of engine takes on. Also specifies the other
  blessed annotations (`@throws`, `@total`) and the verdict vocabulary
  (SZS statuses).
- **`fixtures/`** — conformance fixtures: annotation strings that every
  implementation must accept or reject. Directory membership is the
  expectation.

## Implementations

The reference implementation of the grammar — file discovery, `@ensures`
extraction, and prefix/formula parsing — lives in [`lemma/`](../lemma/) at
the repository root, exercised against `fixtures/` in CI. Two engines
build on it, one from each side of the proofs-and-refutations dialectic:

- [`engines/pabst/`](../engines/pabst/) (TypeScript) — the **refutation
  engine**: compiles properties to
  [fast-check](https://fast-check.dev/) runs and hunts for
  counterexamples.
- [`engines/thales/`](../engines/thales/) (Lean 4) — the **proof
  engine**: compiles the annotated code to Lean and attempts to prove each
  property for all inputs.

The lakatos frontend at the repository root runs both.

## The name

From lemma-incorporation in Imre Lakatos's *Proofs and Refutations*: a
proof survives a counterexample by making a hidden assumption explicit as a
lemma. That is this toolchain's workflow — the refuter finds the
counterexample, you strengthen the property, the prover establishes the
repaired claim. An `@ensures` block simply is a lemma stated about a
function.

## Status

Early. The grammar is real and shipped (extracted from pabst, where it was
developed); the semantics document is a skeleton being filled in; the
fixture corpus is a verified seed, run in CI against the shared parser in
`lemma/`. Planned next: golden parse trees for the fixtures once the AST
is canonicalized. (The parser is a module of this repository's root
package; there is no separate reference-parser package.)

## License

MIT.
