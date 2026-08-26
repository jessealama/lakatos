# Thales

The proof engine of [lakatos](../../README.md). Thales maps TypeScript
programs and their Lemma annotations (`@ensures`, `@throws`, `@total`) to
Lean 4 and attempts proofs, reporting one SZS verdict per annotation.

Thales accepts essentially all TypeScript. That does not mean all of
TypeScript maps cleanly to Lean: constructs outside the mappable subset
degrade gracefully — only the annotations whose proofs depend on them are
reported as `Inappropriate` (with the offending construct named), and every
other annotation still gets a real proof attempt.

## Architecture

The engine is elaboration-based, in the language-oriented-programming
tradition:

1. **Front end (TypeScript).** The TS compiler API parses the target file;
   each declaration it can model becomes per-declaration JSON, which the
   `thales-emit` executable renders as ordinary Lean — a `def` per function
   in a computable monad, a `#thales_prove` command per annotation. What it
   cannot model it classifies itself, naming the offending construct, so
   nothing unmappable reaches Lean.
2. **ThalesDsl (Lean).** `#thales_prove` states each annotation's theorem,
   runs the proof ladder (`decide` over bounded domains, then generic
   tactics), and prints one JSON verdict line to stdout.
3. **CLI (`lakatos prove`).** Collects the verdict lines and assembles the
   standard per-annotation envelope.

The engine is mid-rewrite; the previous whole-file subset-checking compiler
has been removed and the layers above are landing slice by slice.

## Building

```bash
lake build
```
